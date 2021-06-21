from chcexperiment import *


class SingleIntArgExperiment(CHCExperiment):
    name = 'single_int_arg'
    vars = {
        'arg0': 'Int',
        'ret': 'Int',
        'call_result': 'Int',
        'call_ex_status': 'Bool',
        'is_error': 'Bool',
    }

    recursion_root_args = ['arg0', 'ret']
    recursion_arg_types = ['Int', 'Int']
    result_args = ['arg0']
    result_arg_types = ['Int']

    def state(self):
        return f'''
(and 
(= {NORMAL_NO_RECURSION} (or (< arg0 0) (> arg0 {self.bound}) ))
(= is_error (= call_result 17))
(= {NORMAL_RECURSION} (and (not {NORMAL_NO_RECURSION}) (not is_error) ))
(= {EXCEPTIONAL} (and (not {NORMAL_NO_RECURSION})  is_error ))

(or 
(and {NORMAL_NO_RECURSION} (= ret arg0) (= ex_status false))
(and 
    {self.recursion_predicate_root_app(
            '(+ 5 arg0)',
            'call_result',
            depth='(+ depth 1)',
            ex_status='call_ex_status'
        )}
    (or 

    (and 
        {NORMAL_RECURSION}
         (= ret  
             (+ (- 6) call_result)
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


if __name__ == '__main__':
    case = SingleIntArgExperiment('100')
    case.run()
