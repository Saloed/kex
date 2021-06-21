import os
import time


class Z3Solver:
    name = 'z3'

    def run(self, query: str, model: str) -> float:
        start = time.time()
        os.system(f'z3 {query} > {model}')
        end = time.time()
        return end - start

    def mk_smtlib_command(self, query):
        return f'''
                (set-logic HORN)
                (set-option :fp.engine spacer)

                {query}

                (check-sat)
                (get-model)
                (get-info :reason-unknown)
                '''


class HoiceSolver:
    name = 'hoice'

    def run(self, query: str, model: str) -> float:
        start = time.time()
        os.system(f'~/CLionProjects/hoice/target/release/hoice {query} > {model}')
        end = time.time()
        return end - start

    def mk_smtlib_command(self, query):
        return f'''
                {query}

                (check-sat)
                (get-model)
                '''
