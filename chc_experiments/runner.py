from multiprocessing import Pool, Lock

from array import ArrayExperiment
from chc_experiments.chcexperiment import CHCExperiment
from single_int_arg import SingleIntArgExperiment
from two_int_args import TwoIntArgsExperiment

experiments = [
    SingleIntArgExperiment('100'),
    SingleIntArgExperiment('300'),
    TwoIntArgsExperiment('100'),
    TwoIntArgsExperiment('200'),
    ArrayExperiment('40'),
    ArrayExperiment('50'),
    # SingleIntArgExperiment('100', solver=HoiceSolver())
]

stats_lock = Lock()


def run_experiment(experiment: CHCExperiment):
    experiment_name, elapsed_time = experiment.run()
    with stats_lock:
        with open('stats.txt', 'w+') as stats:
            stats.write(f'{experiment_name} -- {elapsed_time}\n')


def run():
    with Pool(6) as pool:
        pool.map(run_experiment, experiments, chunksize=1)


if __name__ == '__main__':
    run()
