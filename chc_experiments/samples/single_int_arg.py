from chc_experiments.chcexperiment import *


class SingleIntArg(object):
    name = 'single_int_arg'
    vars = {
        'arg0': 'Int',
        'ret': 'Int',
        'call_result': 'Int',
        'is_error': 'Bool',
    }

    recursion_root_args = ['arg0', 'ret']
    recursion_arg_types = ['Int', 'Int']
    result_args = ['arg0']
    result_arg_types = ['Int']
    result_status = 0

    def state(self):
        return f'''
(and
(= {NORMAL_NO_RECURSION} (or (< arg0 0) (> arg0 {self.bound}) ))
(= is_error (or (= call_result 17)  ))
(= {NORMAL_RECURSION} (and (not {NORMAL_NO_RECURSION}) (not is_error) ))
(= {EXCEPTIONAL} (and (not {NORMAL_NO_RECURSION})  is_error ))

(or
(and {NORMAL_NO_RECURSION} (= ret arg0) (= {EX_STATUS} {self.ex_status_value(0)}))
(and
    {self.recursion_predicate_transition(
            '(+ 5 arg0)',
            'call_result',
        )}
    (or

    (and
        {NORMAL_RECURSION}
         (= ret
             (+ (- 6) call_result)
         )
         (= {EX_STATUS} {CALL_EX_STATUS})
    )
    (and
        {EXCEPTIONAL}
         (or
            (and (= call_result 17) (= {EX_STATUS} {self.ex_status_value(1)}))
         )
         (= ret 0)
    )
    )
)
)
)
'''
