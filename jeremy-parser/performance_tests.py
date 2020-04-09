from proof_reader import preprocess, construct_node, check_arity, logger
from constants import *
import pickle
import time

PERF = 25
logger.setLevel(PERF)


class TimerError(Exception):
    """A custom exception used to report errors in use of Timer class"""


class Timer:
    def __init__(self):
        self._start_time = None

    def start(self, label):
        """Start a new timer"""
        if self._start_time is not None:
            raise TimerError(f"Timer is running. Use .stop() to stop it")
        self.label = label
        self._start_time = time.perf_counter()

    def stop(self):
        """Stop the timer, and report the elapsed time"""
        if self._start_time is None:
            raise TimerError(f"Timer is not running. Use .start() to start it")

        elapsed_time = time.perf_counter() - self._start_time
        self._start_time = None
        logger.log(PERF, f"{self.label} took: {elapsed_time:0.4f} seconds.\n")


with open(f'theory-lib/arity_db', 'rb') as f:
    timer = Timer()
    timer.start("load arity db")
    arity_db = pickle.load(f)
    timer.stop()
    logger.log(PERF, f"Loaded arity_db with {len(arity_db)} entries.\n")


def run_performance_test(code, name):
    logger.log(PERF, f"Performance test for {name}.\n")
    overall_timer = Timer()
    overall_timer.start("overall")
    timer = Timer()
    timer.start("preprocess")
    s = preprocess(code)
    timer.stop()

    timer.start("construct_node")
    t = construct_node(s, LABEL_DOCUMENT)
    timer.stop()

    timer.start("check_arity")
    warnings, _ = check_arity(t, arity_db)
    timer.stop()
    overall_timer.stop()


with open(f'test_data/performance_tests/perf1.v', 'r') as f:
    run_performance_test(f.read(), "perf1")
