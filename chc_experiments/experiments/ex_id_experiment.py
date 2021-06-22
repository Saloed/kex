from chc_experiments.chcexperiment import *


class ExIdExperiment(CHCExperiment):
    vars: Dict[str, str] = {}
    name: str = NotImplemented
    recursion_root_args: List[str] = NotImplemented
    recursion_arg_types: List[str] = NotImplemented
    result_args: List[str] = NotImplemented
    result_arg_types: List[str] = NotImplemented
    prefix: str = 'depth_ex_id'

    base_vars = {
        EX_STATUS: 'Int',
        CALL_EX_STATUS: 'Int',
        **CHCExperiment.base_vars,
    }

    def ex_status_value(self, value: int) -> str:
        return str(value)

    def query(self):
        status = self.ex_status_value(self.result_status)
        return [
            implies(
                f'(and (>= {DEPTH} 0) {NORMAL_NO_RECURSION} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth=DEPTH, ex_status=EX_STATUS)
            ),
            implies(
                f'(and (>= {DEPTH} 0) {NORMAL_RECURSION} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth=DEPTH, ex_status=EX_STATUS)
            ),
            implies(
                f'(and (>= {DEPTH} 0) {EXCEPTIONAL} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth=DEPTH, ex_status=EX_STATUS)
            ),
            implies(
                f'''(and (< {DEPTH} 0)  {
                self.recursion_predicate_root_app(*self.recursion_root_args, depth=DEPTH, ex_status=EX_STATUS)
                })''',
                'false'
            ),
            implies(self.result_predicate(), self.root_recursion('0', status)),
            implies(self.root_recursion('0', status), self.result_predicate()),
            implies(
                f'''(and {self.result_predicate()} (not (= {EX_STATUS} {status})) {
                self.root_recursion('0', EX_STATUS)
                })''',
                'false'
            ),
        ]
