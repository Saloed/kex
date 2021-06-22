from chc_experiments.chcexperiment import *


class TwoIntArgs(object):
    name = 'two_int_args'
    vars = {
        'arg0': 'Int',
        'arg1': 'Int',
        'ret': 'Int',
        'call_result': 'Int',
        'is_error': 'Bool',
    }

    recursion_root_args = ['arg0', 'arg1', 'ret']
    recursion_arg_types = ['Int', 'Int', 'Int']
    result_args = ['arg0', 'arg1']
    result_arg_types = ['Int', 'Int']
    result_status = 0

    def state(self):
        return f'''
(and 
(= {NORMAL_NO_RECURSION} (or (< arg0 0) (> arg0 {self.bound}) (< arg1 0) (> arg1 {self.bound})))
(= is_error (= call_result 17))
(= {NORMAL_RECURSION} (and (not {NORMAL_NO_RECURSION}) (not is_error) ))
(= {EXCEPTIONAL} (and (not {NORMAL_NO_RECURSION})  is_error ))

(or 
(and {NORMAL_NO_RECURSION} (= ret (+ arg0 arg1)) (= {EX_STATUS} {self.ex_status_value(0)}))
(and 
    {self.recursion_predicate_transition(
            '(+ 5 arg0)',
            '(+ 5 arg1)',
            'call_result'
        )}
    (or 

    (and 
        {NORMAL_RECURSION}
         (= ret  
             (+ (- 11) call_result)
         ) 
         (= {EX_STATUS} {CALL_EX_STATUS}) 
    )
    (and 
        {EXCEPTIONAL}
         (= {EX_STATUS} {self.ex_status_value(1)})
         (= ret 0)
    )   
    )
)
)
)
'''
