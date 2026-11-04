"""Two independent native queues for the agent and the tool service."""
from contextlib import contextmanager

from .bridge import NativeBridge


@contextmanager
def native_pair(binary, authorization_file=None):
    with NativeBridge(binary, authorization_file) as agent,\
         NativeBridge(binary, authorization_file) as server:
        if agent.process.pid == server.process.pid or agent.lock is server.lock:
            raise ValueError("native_roles_share_process_or_queue")
        agent.role, server.role = "agent", "server"
        agent.command("set_role", role="agent")
        server.command("set_role", role="server")
        yield agent, server


def process_record(agent, server):
    if agent.process.pid == server.process.pid or agent.lock is server.lock:
        raise ValueError("native_roles_share_process_or_queue")
    agent_meta, server_meta = agent.command("metadata"), server.command("metadata")
    if (agent_meta.get("role") != "agent" or server_meta.get("role") != "server"
            or agent_meta.get("process_id") != agent.process.pid
            or server_meta.get("process_id") != server.process.pid
            or server_meta.get("private_instance_count") != 0
            or server_meta.get("shared_parent_count") != 0
            or server_meta.get("darlt_issuer_issue_calls_total") != 0
            or server_meta.get("public_only_installed") is not True):
        raise ValueError("native_role_or_public_only_state_failed")
    return {"agent_pid": agent.process.pid, "server_pid": server.process.pid,
            "different_processes": True, "different_command_locks": True,
            "agent_metadata": agent_meta, "server_metadata": server_meta}
