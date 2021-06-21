from chcexperiment import *


class TwoIntArgsExperiment(CHCExperiment):
    name = 'two_int_args'
    vars = {
        'arg0': 'Int',
        'arg1': 'Int',
        'ret': 'Int',
        'call_result': 'Int',
        'call_ex_status': 'Bool',
        'is_error': 'Bool',
    }

    recursion_root_args = ['arg0', 'arg1', 'ret']
    recursion_arg_types = ['Int', 'Int', 'Int']
    result_args = ['arg0', 'arg1']
    result_arg_types = ['Int', 'Int']

    def state(self):
        return f'''
(and 
(= {NORMAL_NO_RECURSION} (or (< arg0 0) (> arg0 {self.bound}) (< arg1 0) (> arg1 {self.bound})))
(= is_error (= call_result 17))
(= {NORMAL_RECURSION} (and (not {NORMAL_NO_RECURSION}) (not is_error) ))
(= {EXCEPTIONAL} (and (not {NORMAL_NO_RECURSION})  is_error ))

(or 
(and {NORMAL_NO_RECURSION} (= ret (+ arg0 arg1)) (= ex_status false))
(and 
    {self.recursion_predicate_root_app(
            '(+ 5 arg0)',
            '(+ 5 arg1)',
            'call_result',
            depth='(+ depth 1)',
            ex_status='call_ex_status'
        )}
    (or 

    (and 
        {NORMAL_RECURSION}
         (= ret  
             (+ (- 11) call_result)
         ) 
         (= ex_status call_ex_status) 
    )
    (and 
        {EXCEPTIONAL}
         (= ex_status true)
         (= ret 0)
    )   
    )
)
)
)
'''
