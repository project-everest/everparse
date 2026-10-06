"""One concurrency budget for build, compiler, and driver subprocesses."""

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import os
import re
import stat
import sys

from corpus import HarnessError


class JobBudget:
    def __init__(self, jobs=None):
        self.reader = self.writer = None
        self.implicit_available = True
        auth = re.findall(r"(?:^|\s)--jobserver-(?:auth|fds)=(\S+)",
                          os.environ.get("MAKEFLAGS", ""))
        if auth:
            try:
                self._connect(auth[-1])
            except (OSError, ValueError) as error:
                self.close()
                raise HarnessError(f"cannot use GNU Make jobserver: {error}; "
                                   "invoke the runner from a '+' recipe") from error
        self.jobs = jobs if jobs is not None else (
            (os.cpu_count() or 1) if self.reader is not None else 1)
        if self.jobs <= 0:
            self.close()
            raise HarnessError("jobs must be positive")

    def _connect(self, auth):
        if auth.startswith("fifo:"):
            path = auth.removeprefix("fifo:")
            self.reader = os.open(path, os.O_RDONLY | os.O_NONBLOCK)
            if not stat.S_ISFIFO(os.fstat(self.reader).st_mode):
                raise ValueError("jobserver path is not a FIFO")
            self.writer = os.open(path, os.O_WRONLY | os.O_NONBLOCK)
        else:
            read_fd, write_fd = map(int, auth.split(","))
            if not all(stat.S_ISFIFO(os.fstat(fd).st_mode) for fd in (read_fd, write_fd)):
                raise ValueError("jobserver descriptors are not pipes")
            # Reopening creates an independent file description. Setting
            # O_NONBLOCK on a dup would also change make's own pipe reader.
            if sys.platform != "linux":
                raise ValueError("pipe jobservers require Linux; use a FIFO jobserver")
            self.reader = os.open(f"/proc/self/fd/{read_fd}", os.O_RDONLY | os.O_NONBLOCK)
            self.writer = os.dup(write_fd)

    def acquire(self):
        if self.implicit_available:
            self.implicit_available = False
            return b""
        if self.reader is None:
            return b""
        try:
            token = os.read(self.reader, 1)
        except BlockingIOError:
            return None
        if not token:
            raise HarnessError("GNU Make jobserver closed while work remained")
        return token

    def release(self, token):
        if token:
            os.write(self.writer, token)
        else:
            self.implicit_available = True

    def close(self):
        for fd in (self.reader, self.writer):
            if fd is not None:
                os.close(fd)
        self.reader = self.writer = None

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


def run_jobs(jobs, budget):
    """Yield (key, result); only the caller updates shared reports."""
    pending = iter(jobs)
    active = {}
    exhausted = False
    with ThreadPoolExecutor(max_workers=budget.jobs) as executor:
        try:
            while active or not exhausted:
                while not exhausted and len(active) < budget.jobs:
                    token = budget.acquire()
                    if token is None:
                        break
                    try:
                        key, action = next(pending)
                    except StopIteration:
                        budget.release(token)
                        exhausted = True
                        break
                    except BaseException:
                        budget.release(token)
                        raise
                    try:
                        future = executor.submit(action)
                    except BaseException:
                        budget.release(token)
                        raise
                    active[future] = (key, token)
                if active:
                    done, _ = wait(active, timeout=0.05, return_when=FIRST_COMPLETED)
                    for future in done:
                        key, token = active.pop(future)
                        budget.release(token)
                        yield key, future.result()
        finally:
            # Do not return slots while their subprocesses are still running,
            # including when an unexpected worker exception aborts the run.
            wait(active)
            for _, token in active.values():
                budget.release(token)
