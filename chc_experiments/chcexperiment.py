import abc
import os
from typing import List, Dict

from solver import Z3Solver

RECURSION_PREDICATE = 'recursion_predicate'
RESULT_PREDICATE = 'result_predicate'
NORMAL_NO_RECURSION = 'normal_no_rec'
NORMAL_RECURSION = 'normal_rec'
EXCEPTIONAL = 'exceptional'
DEPTH = 'depth'
EX_STATUS = 'ex_status'


def _implies(a, b):
    return f'(=> {a} {b})'


def _ensure_dir(dir_name):
    if not os.path.exists(dir_name):
        os.makedirs(dir_name)


class CHCExperiment(abc.ABC):
    vars: Dict[str, str] = {}
    name: str = NotImplemented
    recursion_root_args: List[str] = NotImplemented
    recursion_arg_types: List[str] = NotImplemented
    result_args: List[str] = NotImplemented
    result_arg_types: List[str] = NotImplemented
    result_status: bool = False
    prefix: str = 'depth_ex_status'

    def state(self) -> str:
        return NotImplemented

    def __init__(self, bound, solver=None):
        self.bound = bound
        self.solver = solver or Z3Solver()

    base_vars = {
        DEPTH: 'Int',
        EX_STATUS: 'Bool',
        NORMAL_NO_RECURSION: 'Bool',
        NORMAL_RECURSION: 'Bool',
        EXCEPTIONAL: 'Bool',
    }

    def recursion_predicate_root_app(self, *args, depth, ex_status) -> str:
        all_args = ' '.join(args + (depth, ex_status))
        return f'({RECURSION_PREDICATE} {all_args})'

    def _result_predicate(self):
        args = ' '.join(self.result_args)
        return f'({RESULT_PREDICATE} {args})'

    def _root_recursion(self, depth, ex_status):
        return self.recursion_predicate_root_app(*self.recursion_root_args, depth=depth, ex_status=ex_status)

    def _query(self):
        return [
            _implies(
                f'(and (>= {DEPTH} 0) {NORMAL_NO_RECURSION} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth="depth", ex_status="false")
            ),
            _implies(
                f'(and (>= {DEPTH} 0) {NORMAL_RECURSION} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth="depth", ex_status="call_ex_status")
            ),
            _implies(
                f'(and (>= {DEPTH} 0) {EXCEPTIONAL} {self.state()})',
                self.recursion_predicate_root_app(*self.recursion_root_args, depth="depth", ex_status="true")
            ),
            _implies(
                f'''(and (< {DEPTH} 0) {
                self.recursion_predicate_root_app(*self.recursion_root_args, depth="depth", ex_status="true")
                })''',
                'false'
            ),
            _implies(self._result_predicate(), self._root_recursion('0', str(self.result_status).lower())),
            _implies(self._root_recursion('0', str(self.result_status).lower()), self._result_predicate()),
            _implies(
                f'''(and {self._result_predicate()} {
                self._root_recursion('0', str(not self.result_status).lower())
                })''',
                'false'
            ),
        ]

    def run(self):
        name = f'{self.solver.name}_{self.prefix}_{self.name}_{self.bound}'
        print(f'start {name}')
        query_name = f'{name}.smtlib'
        model_name = f'{name}_model.txt'

        raw_query = self._mk_query()
        query_txt = self.solver.mk_smtlib_command(raw_query)

        _ensure_dir('queries')
        _ensure_dir('models')

        query_path = os.path.join('queries', query_name)
        model_path = os.path.join('models', model_name)

        with open(query_path, 'w') as qf:
            qf.write(query_txt)

        elapsed = self.solver.run(query_path, model_path)
        print(f'{name} -- {elapsed}')
        return name, elapsed

    def _var_decls(self):
        all_vars = self.vars.copy()
        all_vars.update(self.base_vars)
        return ' '.join(f'({name} {var_type})' for name, var_type in all_vars.items())

    def _predicate_def(self, name, predicate_type):
        return f'(declare-fun {name} ({predicate_type}) Bool)'

    def _assert_forall(self, query):
        return f'(assert (forall ({self._var_decls()}) {query}))'

    def _mk_query(self):
        query_str = '\n'.join(self._assert_forall(it) for it in self._query())
        recursion_pred_type = ' '.join(self.recursion_arg_types + [self.base_vars[DEPTH], self.base_vars[EX_STATUS]])
        return f'''
        {self._predicate_def(RECURSION_PREDICATE, recursion_pred_type)}
        {self._predicate_def(RESULT_PREDICATE, ' '.join(self.result_arg_types))}
        {query_str}
        '''
