"""Private local control channel to the independent native crypto executable."""
from __future__ import annotations

import os
import subprocess
import threading
from pathlib import Path
from .common import canonical, strict


class NativeBridge:
    def __init__(self, binary, authorization_file=None):
        self.authorization_file = str(Path(authorization_file).resolve()) if authorization_file else None
        env = {"PATH": os.environ.get("PATH", ""), "RAYON_NUM_THREADS": "1", "OMP_NUM_THREADS": "1"}
        self.process = subprocess.Popen([str(Path(binary).resolve())], stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                        text=True, bufsize=1, env=env)
        self.lock = threading.RLock()

    def command(self, op, **values):
        request = {"op": op, **values}
        if self.authorization_file:
            request.update(timing=True, authorization_file=self.authorization_file)
        with self.lock:
            if self.process.poll() is not None:
                raise ValueError("native_bridge_unavailable")
            self.process.stdin.write(canonical(request).decode() + "\n")
            self.process.stdin.flush()
            line = self.process.stdout.readline()
            if not line:
                raise ValueError("native_bridge_no_response")
            response = strict(line)
        if response.get("ok") is not True:
            raise ValueError(response.get("error", "native_rejected"))
        return response["result"]

    def close(self):
        with self.lock:
            if self.process.poll() is None:
                self.process.stdin.close()
                try:
                    self.process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    self.process.kill(); self.process.wait(timeout=5)
            self.process.stdout.close()

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()
