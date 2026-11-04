"""Atomic quota/serial consumption and synthetic hotel effects in SQLite."""
from __future__ import annotations

from contextlib import contextmanager
from pathlib import Path
import sqlite3
from .common import canonical, strict, COSTS, DOCUMENT_IDS, RESEARCH, normalize, policy


class Denied(ValueError):
    pass


class Store:
    def __init__(self, path):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self.connect() as db:
            db.executescript("""
                CREATE TABLE IF NOT EXISTS grants(namespace TEXT PRIMARY KEY,subject TEXT NOT NULL,
                    scopes BLOB NOT NULL,attributes BLOB NOT NULL,remaining INTEGER NOT NULL CHECK(remaining>=0),
                    jkt TEXT,period INTEGER NOT NULL);
                CREATE TABLE IF NOT EXISTS consumed(namespace TEXT NOT NULL,serial TEXT NOT NULL,
                    request TEXT NOT NULL,PRIMARY KEY(namespace,serial));
                CREATE TABLE IF NOT EXISTS dpop(namespace TEXT NOT NULL,jti TEXT NOT NULL,PRIMARY KEY(namespace,jti));
                CREATE TABLE IF NOT EXISTS bookings(id INTEGER PRIMARY KEY AUTOINCREMENT,item TEXT NOT NULL,customer TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS effects(id INTEGER PRIMARY KEY AUTOINCREMENT,namespace TEXT NOT NULL,
                    tool TEXT NOT NULL,args BLOB NOT NULL,units INTEGER NOT NULL,request TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS research(namespace TEXT PRIMARY KEY,stage INTEGER NOT NULL,
                    documents INTEGER NOT NULL,rows INTEGER NOT NULL,report_complete INTEGER NOT NULL);
            """)

    @contextmanager
    def connect(self):
        db = sqlite3.connect(self.path, isolation_level=None, timeout=30)
        db.execute("PRAGMA journal_mode=WAL")
        db.execute("PRAGMA synchronous=FULL")
        try:
            yield db
        finally:
            db.close()

    def install_grant(self, namespace, subject="agent", quota=64, scopes=None,
                      attributes=(0, 1, 2, 3), jkt=None, period=1):
        if type(quota) is not int or quota < 0:
            raise ValueError("grant_quota")
        scopes = ([name + ":inventory/allowed" for name in COSTS if name not in ("delete_record", "export_private")]
                  if scopes is None else scopes)
        with self.connect() as db:
            db.execute("INSERT INTO grants VALUES(?,?,?,?,?,?,?)", (namespace, subject,
                       canonical(scopes), canonical(list(attributes)), quota, jkt, period))

    def snapshot(self):
        # A deep database backup, never a shared mutable connection.
        target = sqlite3.connect(":memory:")
        with self.connect() as source:
            source.backup(target)
        return target

    def restore(self, snapshot):
        with self.connect() as target:
            snapshot.backup(target)

    def facts(self, namespace=None):
        with self.connect() as db:
            effects = db.execute("SELECT COUNT(*) FROM effects" + (" WHERE namespace=?" if namespace else ""),
                                 (namespace,) if namespace else ()).fetchone()[0]
            bookings = db.execute("SELECT COUNT(*) FROM bookings").fetchone()[0]
            consumed = db.execute("SELECT COUNT(*) FROM consumed" + (" WHERE namespace=?" if namespace else ""),
                                  (namespace,) if namespace else ()).fetchone()[0]
            remaining = db.execute("SELECT remaining FROM grants WHERE namespace=?", (namespace,)).fetchone() if namespace else None
        return {"effects": effects, "bookings": bookings, "consumed": consumed,
                "remaining": remaining[0] if remaining else None}

    def research_facts(self, namespace):
        with self.connect() as db:
            row = db.execute("SELECT stage,documents,rows,report_complete FROM research WHERE namespace=?", (namespace,)).fetchone()
        return dict(zip(("stage", "documents", "rows", "report_complete"), row or (0, 0, 0, 0)))

    @staticmethod
    def _research(db, namespace, tool, arguments):
        row = db.execute("SELECT stage,documents,rows,report_complete FROM research WHERE namespace=?", (namespace,)).fetchone()
        stage, documents, rows, complete = row or (0, 0, 0, 0)
        expected = RESEARCH.index(tool)
        if stage != expected:
            raise Denied("research_sequence")
        dataset = [{"row_id": i, "value": 10 * i} for i in range(1, 17)]
        values = [row["value"] for row in dataset]
        analysis = {"sum": sum(values), "mean": sum(values) / len(values), "minimum": min(values), "maximum": max(values)}
        if tool == "search_sources":
            result = {"sources": [{"document_id": item, "title": "Local market source " + item} for item in DOCUMENT_IDS],
                      "document_ids": list(DOCUMENT_IDS), "source_count": 8, "query": arguments["query"]}
        elif tool == "fetch_documents":
            documents = 8
            result = {"documents": [{"document_id": item, "text": "Deterministic market evidence " + item} for item in arguments["document_ids"]],
                      "document_count": documents, "dataset_id": "market-v1"}
        elif tool == "query_dataset":
            if documents != 8:
                raise Denied("research_documents_missing")
            rows = 16
            result = {"dataset_id": "market-v1", "rows": dataset, "row_count": rows, "document_count": documents}
        elif tool == "run_analysis":
            if rows != 16:
                raise Denied("research_dataset_missing")
            result = {"analysis_id": "analysis-001", "dataset_id": "market-v1", "operation_count": 4,
                      "row_count": rows, "document_count": documents, "summary": analysis}
        else:
            if documents != 8 or rows != 16:
                raise Denied("research_analysis_missing")
            complete = 1
            result = {"report_id": "report-001", "analysis_id": "analysis-001", "complete": True,
                      "section_count": 32, "document_count": documents, "row_count": rows,
                      "summary": analysis,
                      "sections": [{"section": i, "status": "complete"} for i in range(1, 33)]}
        db.execute("INSERT INTO research VALUES(?,?,?,?,?) ON CONFLICT(namespace) DO UPDATE SET stage=excluded.stage,documents=excluded.documents,rows=excluded.rows,report_complete=excluded.report_complete",
                   (namespace, stage + 1, documents, rows, complete))
        return result

    def commit(self, mode, namespace, tool, arguments, request_id, serials=(), claims=None,
               dpop_jti=None, inject_failure=False):
        args = normalize(tool, arguments); cost = COSTS[tool]
        if len(set(serials)) != len(serials):
            raise Denied("duplicate_unit_in_batch")
        if mode in ("darlt", "darlt-ablation", "sma") and len(serials) != cost:
            raise Denied("wrong_native_unit_count")
        try:
            with self.connect() as db:
                db.execute("BEGIN IMMEDIATE")
                try:
                    if mode in ("oauth", "msb", "slw"):
                        grant = db.execute("SELECT subject,scopes,attributes,remaining,jkt,period FROM grants WHERE namespace=?", (namespace,)).fetchone()
                        if grant is None:
                            raise Denied("unknown_grant")
                        subject, scopes, attrs, remaining, jkt, period = grant
                        scopes, attrs = strict(scopes), strict(attrs)
                        resources = [args["resource"]]
                        if tool == "batch_query":
                            resources.extend(x["resource"] for x in args["items"])
                        if any(tool + ":" + resource not in scopes for resource in resources):
                            raise Denied("scope_not_granted")
                        required = policy(tool, args, period)["required_attrs"]
                        if any(x["index"] not in attrs or x["index"] >= 6 for x in required):
                            raise Denied("attribute_not_granted")
                        if mode == "oauth":
                            if claims is None or claims["sub"] != subject or claims["cnf"]["jkt"] != jkt or claims["period"] != period:
                                raise Denied("grant_binding")
                            if not isinstance(dpop_jti, str) or not dpop_jti:
                                raise Denied("dpop_jti_missing")
                            db.execute("INSERT INTO dpop VALUES(?,?)", (namespace, dpop_jti))
                        if remaining < cost:
                            raise Denied("quota_exhausted")
                        db.execute("UPDATE grants SET remaining=remaining-? WHERE namespace=?", (cost, namespace))
                    for serial in serials:
                        db.execute("INSERT INTO consumed VALUES(?,?,?)", (namespace, serial, request_id))
                    if tool in RESEARCH:
                        result = self._research(db, namespace, tool, args)
                    elif tool == "book_item":
                        cur = db.execute("INSERT INTO bookings(item,customer) VALUES(?,?)", (args["item_id"], args["customer"]))
                        result = {"booking_id": cur.lastrowid, "item_id": args["item_id"], "customer": args["customer"]}
                    elif tool in ("search_inventory", "batch_query", "get_details"):
                        count = db.execute("SELECT COUNT(*) FROM bookings WHERE item=?", ("hotel-101",)).fetchone()[0]
                        item = {"item_id": "hotel-101", "name": "Local Hotel", "bookings": count}
                        result = {"items": [item] * 8} if tool == "batch_query" else {"items": [item]} if tool == "search_inventory" else item
                    else:
                        result = {"operation": tool, "synthetic": True}
                    db.execute("INSERT INTO effects(namespace,tool,args,units,request) VALUES(?,?,?,?,?)",
                               (namespace, tool, canonical(args), cost, request_id))
                    if inject_failure:
                        raise Denied("injected_backend_failure")
                    db.execute("COMMIT")
                    return {"tool_result": result, "units": cost, "accepted": True}
                except BaseException:
                    db.execute("ROLLBACK")
                    raise
        except sqlite3.IntegrityError as exc:
            raise Denied("serial_or_dpop_replay") from exc
