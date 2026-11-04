# DARLT: Delegatable Anonymous Rate-Limited Tokens With Batch Spending and Public Accountability for AI Agents

This repository implements SPSEQ-FC and DARLT on BLS12-381, together with the paper's comparison schemes and experiments. SPSEQ-FC signs equivalence classes of functional commitments. DARLT issues a period budget, delegates selected pools and attributes to agents, and spends several units in one token.

This is a research prototype for reproducing the paper’s results; it has not been audited for production use.

## Contributions

- SPSEQ-FC signatures, re-randomization, functional openings and verification.
- DARLT pool delegation, attribute policies, batch spending, a secret metadata bit and public identification of conflicting spends or allocations.
- A common Rust evaluation of ten schemes and an MCP case study with booking and research workflows, atomic SQLite consumption and tool execution.

## Build and test

The experiments use an Apple M2 Pro (aarch64), 32 GiB memory, macOS 14.6.1 and Rust 1.94.1. `rust-toolchain.toml` selects Rust 1.94.1; the crates include `Cargo.lock`. Group arithmetic uses `blstrs` 0.7.1 and `blst` 0.3.17. LCB24 generates Groth16 proofs with Arkworks 0.3 and verifies them with `blstrs`. Native computation runs in one thread.

Python 3.11 dependencies for plots and the case study:

```sh
python3 -m pip install numpy==2.2.6 matplotlib==3.8.4 httpx==0.28.1 cryptography==41.0.3 PyMuPDF==1.27.1
```

Build and check the core implementation:

```sh
cargo build --locked --release
cargo test --locked --workspace --release
cargo fmt --all -- --check
cargo clippy --locked --workspace --all-targets --release -- -D warnings
```

Build and test the e-cash adapters:

```sh
SSL_CERT_FILE="$(python3 -m certifi)" python3 ecash/lcb24/fetch_sources.py
cargo test --locked --release --manifest-path ecash/lcb24/Cargo.toml
cargo test --locked --release --manifest-path ecash/rp23/Cargo.toml
```

The LCB24 source helper downloads four author modules at a fixed revision and checks their SHA-256 hashes. The modules are stored in `source-cache/` for compilation. Source attribution and revisions are listed in `NOTICE`.

## Reproduce the figures and tables

Reproduce all figures, tables and the selected paper values from the included data:

```sh
python3 scripts/reproduce.py all
```

Each figure command exports panel CSVs, PDFs and PNGs. The Fig. 12 command also produces a combined preview.

| Result | Command | Main output |
| --- | --- | --- |
| Fig. 7: algorithm and communication cost | `python3 scripts/reproduce.py figure7` | `outputs/figure7/fig7a.pdf`, `fig7b.pdf` |
| Fig. 8: attribute and range-width scans | `python3 scripts/reproduce.py figure8` | `outputs/figure8/fig8a.pdf`, `fig8b.pdf` |
| Fig. 9: delegation cost and issuer cost for $A$ agents | `python3 scripts/reproduce.py figure9` | `outputs/figure9/fig9a.pdf`, `fig9b.pdf` |
| Fig. 10: batch verification and communication | `python3 scripts/reproduce.py figure10` | `outputs/figure10/fig10a.pdf`, `fig10b.pdf` |
| Fig. 11: online BatchSpend and BatchVerify across attributes | `python3 scripts/reproduce.py figure11` | `outputs/figure11/fig11a.pdf`, `fig11b.pdf` |
| Fig. 12: workflows and deployments | `python3 scripts/reproduce.py figure12` | `outputs/figure12/fig12.pdf` |
| Table III: communication cost | `python3 scripts/reproduce.py table3` | `outputs/table3/table3.csv` |
| Table IV: time cost of the protocols | `python3 scripts/reproduce.py table4` | `outputs/table4/table4.csv`, `table_iv_totals.csv` |
| Table V: misuse cases | `python3 scripts/reproduce.py table5` | `outputs/table5/table_v_cases.csv` |
| One selected result per task | `python3 scripts/reproduce.py paper-values` | `outputs/paper-values/paper_values.csv` |

For each task group, the figures use the first attempt in which every task met the 5% coefficient-of-variation threshold; nine microbenchmark groups and three case-study groups that never met it use their first attempt.

Fig. 9(b)'s CSV contains the issuer cost, the total cost and the cost per agent. Table IV's Issue total includes the request, issuer response and receipt. Its Delegate total includes user send and agent receipt. Total SD is calculated from paired samples when available. `verification_unit_increment.csv` records `(mean(k=64) − mean(k=16))/48` with both source tasks and attempts.

## MCP case study

The case study compares OAuth 2.0 access JWTs with DPoP, shared-wallet SMA²RT, single-unit DARLT and batch-spending DARLT. An agent and a service execute in separate native processes. The service receives public verifier material; token consumption and tool effects are committed atomically in SQLite. The MCP profile uses protocol version `2026-07-28`.

| Workflow | Tool sequence | Units | Delegated budget |
| --- | --- | --- | --- |
| Booking | Search inventory, get details, book item, get details, search inventory | 1, 1, 4, 1, 1 | 16 |
| Research | Search sources, fetch documents, query dataset, run analysis, export report | 1, 8, 16, 4, 32 | 64 |

Background preparation stocks one token per tool. A used tool is replenished only when it can occur again and unallocated delegated units remain. Replay prepares all required tokens before the first tool demand.

Build the native bridge and run the local checks:

```sh
cargo build --locked --release --manifest-path case_study/native/Cargo.toml
cargo test --locked --release --manifest-path case_study/native/Cargo.toml
python3 -m unittest discover -s case_study -p 'test_*.py'
python3 -m case_study.run --mode check --out outputs/case-check
```

Replay the recorded workflows locally:

```sh
python3 -m case_study.run --mode replay --out outputs/case-replay
```

Redrawing Fig. 12 and Table V uses the included data and needs no API key. Running new live model workflows uses an `OPENROUTER_API_KEY` supplied through the environment:

```sh
python3 -m case_study.run --mode live --out outputs/case-live
```

The model configuration is `google/gemini-3.8-flash`, routed to Google Vertex (`google-vertex/global`) with fallback disabled.

### Minimal protocol flow

The bridge's `init` operation performs Setup, key generation, issuance and delegation. Preparation creates an eight-unit token; verification starts from its encoded bytes.

```python
from case_study.bridge import NativeBridge

policy = {"period": 1, "required_attrs": [{"index": 3, "value": 1}]}
context = "research/fetch-documents/request-1"

with NativeBridge("case_study/native/target/release/darlt-case-study-native") as native:
    native.command("init", scheme="DARLT", instance="research-agent")
    prepared = native.command("prepare", instance="research-agent", actor="agent",
                              k=8, policy=policy)
    token = native.command("online", handle=prepared["handle"],
                           context=context, policy=policy)
    result = native.command("verify", instance="research-agent",
                            wire_hex=token["wire_hex"], context=context, policy=policy)
    assert result["valid"] and result["unit_count"] == 8
```

## Implemented comparison schemes

| Label | Paper and venue | Implementation source |
| --- | --- | --- |
| SMA²RT | [SMA²RT: Secret-Metadata Attribute-Based Anonymous Rate-Limited Tokens](https://eprint.iacr.org/2026/518), CRYPTO 2026 | Rust implementation |
| BHN+26 (`NIAT`) | [Non-interactive Anonymous Tokens with Private Metadata Bit](https://eprint.iacr.org/2025/430), ACM CCS 2026 | Rust implementation |
| KLO26 (`CPAT`) | [Completing Policy-based Anonymous Tokens: Private Bits, Public Metadata and more…](https://doi.org/10.1145/3779208.3785269), ASIA CCS 2026 | Rust implementation |
| TJH+26 (`HinToken`) | [Anonymous Tokens with Designated-Reader Metadata Bit](https://www.usenix.org/conference/usenixsecurity26/presentation/tu), USENIX Security 2026 | Rust implementation |
| MSB+23 | [Practical Delegatable Anonymous Credentials From Equivalence Class Signatures](https://petsymposium.org/popets/2023/popets-2023-0093.php), PoPETs 2023(3) | Rust implementation |
| SLW+25 | [How to Securely Delegate and Revoke Partial Authorization Credentials](https://doi.org/10.1109/TDSC.2024.3424520), IEEE TDSC 22(2), 2025 | Rust implementation, without revocation |
| RP23-C / RP23-D | [Compact and Divisible E-Cash with Threshold Issuance](https://petsymposium.org/popets/2023/popets-2023-0116.php), PoPETs 2023(4) | Author code adapted to `blstrs` |
| LCB24 | [Divisible E-Cash for Billing in Private Ad Retargeting](https://petsymposium.org/popets/2024/popets-2024-0104.php), PoPETs 2024(4) | Author circuit and Schnorr modules, pinned by commit and SHA-256 |

## Project structure

| File or directory | Contents |
| --- | --- |
| `src/` | SPSEQ-FC, DARLT and common group/state primitives |
| `src/spseq_fc.rs` | SPSEQ-FC key generation, signatures, delegation keys and representative changes |
| `src/darlt/` | DARLT issuance, delegation, spending, verification and recovery |
| `src/common/` | Shared group, encoding and state helpers |
| `baselines/` | Token and delegatable-credential comparison schemes |
| `ecash/` | Compact, divisible and Groth16 e-cash adapters |
| `bench/` | Experiment workers, task catalog, sampling and operation counts |
| `case_study/` | MCP client/server, workflows, OAuth, SQLite and native bridge |
| `scripts/` | Paper-value selection, plots and table exports |
| `data/microbench/` | Microbenchmark records, attempts, statistics and selected values |
| `data/case_study/` | Recorded workflows, replay results and misuse checks |
| `figures/` | The twelve final paper-panel PDFs |
| `tests/` | Integration and correctness tests |
| `Cargo.toml`, `Cargo.lock` | Rust workspace and pinned dependencies |
| `rust-toolchain.toml` | Rust toolchain version |
| `NOTICE` | Source attribution and pinned author-code revisions |

## Data format

Time columns are `mean_ms` and `sample_sd_ms`; SD uses denominator `n−1`. `n`, `attempt`, `source_attempt`, `cohort_status` and `paper_selection_rule` identify the retained result. Task identifiers use the implementation scheme labels shown above. `table_iv_total_*` and `verification_unit_increment_*` columns carry derived totals and their source tasks.

Microbenchmark JSONL records and whole-sample CSVs are gzip-compressed. `paper_values.csv` is the selected task-level dataset. Case-study traces are named `booking-00.json` through `booking-09.json` and `research-00.json` through `research-09.json`. `live_steps.csv` records live workflows; `replay_samples.csv`, `replay_attempts.csv`, `replay_selected.csv` and `replay_steps.jsonl` record replay. `provisioning_issuance.json`, `provisioning_delegations.json` and `provisioning_audit.json` record budget provisioning. Raw segments use `*_ns` columns; Fig. 12 uses milliseconds. Agent latency, native verification and the service's verification/state-commit window have separate fields.

Size CSVs contain encoded bytes. Plot axes use KB, with 1 KB = 1024 B. Issuance requests, responses, delegation deliveries, wallet components and payment information are listed separately. Public-parameter components retain their role and scope. Panel CSVs are exported next to their figures.

## License

Apache-2.0.
