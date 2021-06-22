from multiprocessing import Pool, Lock
from itertools import cycle
from cases import *

experiments = [
    ExStatusSingleIntArg('100'),
    ExStatusSingleIntArg('200'),
    ExStatusTwoIntArgs('100'),
    # ExStatusTwoIntArgs('200'),
    ExStatusArray('40'),
    ExIdSingleIntArg('100'),
    ExIdSingleIntArg('200'),
    ExIdTwoIntArgs('100'),
    # ExIdTwoIntArgs('200'),
    ExIdArray('40'),
]

stats_lock = Lock()


def run_experiment(experiment):
    experiment_name, elapsed_time = experiment.run()
    with stats_lock:
        with open('stats.txt', 'a') as stats:
            stats.write(f'{experiment_name} -- {elapsed_time}\n')


def run():
    with Pool(6) as pool:
        list(pool.imap_unordered(run_experiment, cycle(experiments), chunksize=1))


if __name__ == '__main__':
    run()
