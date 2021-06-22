from experiments.ex_id_experiment import ExIdExperiment
from experiments.ex_status_experiment import ExStatusExperiment

from samples.array import Array
from samples.single_int_arg import SingleIntArg
from samples.two_int_args import TwoIntArgs


class ExIdArray(Array, ExIdExperiment):
    pass


class ExIdSingleIntArg(SingleIntArg, ExIdExperiment):
    pass


class ExIdTwoIntArgs(TwoIntArgs, ExIdExperiment):
    pass


class ExStatusArray(Array, ExStatusExperiment):
    pass


class ExStatusSingleIntArg(SingleIntArg, ExStatusExperiment):
    pass


class ExStatusTwoIntArgs(TwoIntArgs, ExStatusExperiment):
    pass
