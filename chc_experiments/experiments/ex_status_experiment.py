from chc_experiments.chcexperiment import *


class ExStatusExperiment(CHCExperiment):
    vars: Dict[str, str] = {}
    name: str = NotImplemented
    recursion_root_args: List[str] = NotImplemented
    recursion_arg_types: List[str] = NotImplemented
    result_args: List[str] = NotImplemented
    result_arg_types: List[str] = NotImplemented
    prefix: str = 'depth_ex_status'

    base_vars = {
        EX_STATUS: 'Bool',
        CALL_EX_STATUS: 'Bool',
        **CHCExperiment.base_vars,
    }

    def ex_status_value(self, value: int) -> str:
        if value == 0:
            return 'false'
        elif value == 1:
            return 'true'
        else:
            raise Exception('Unexpected status value')

    def query(self):
        status = self.ex_status_value(self.result_status)
        return [
            implies(
                f'(and (>= {DEPTH} 0) {NORMAL_NO_RECURSION} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth=DEPTH, ex_status="false")
            ),
            implies(
                f'(and (>= {DEPTH} 0) {NORMAL_RECURSION} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth=DEPTH, ex_status="call_ex_status")
            ),
            implies(
                f'(and (>= {DEPTH} 0) {EXCEPTIONAL} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth=DEPTH, ex_status="true")
            ),
            implies(
                f'''(and (< {DEPTH} 0) {
                self.recursion_predicate_root_app(*self.recursion_root_args, depth=DEPTH, ex_status=EX_STATUS)
                })''',
                'false'
            ),
            implies(self.result_predicate(), self.root_recursion('0', status)),
            implies(self.root_recursion('0', status), self.result_predicate()),
            implies(
                f'''(and {self.result_predicate()} {
                self.root_recursion('0', '(not ' + status + ')')
                })''',
                'false'
            ),
        ]
