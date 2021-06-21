from chcexperiment import *


class ArrayExperiment(CHCExperiment):
    name = 'array'
    vars = {
        'arg0': 'Int',
        'arg1': '(Array Int Int)',
        'ret': '(Array Int Int)',
        'call_result': '(Array Int Int)',
        'call_ex_status': 'Bool',
        'is_error': 'Bool',
    }

    recursion_root_args = ['arg0', 'arg1', 'ret']
    recursion_arg_types = ['Int', '(Array Int Int)', '(Array Int Int)']
    result_args = ['arg0', 'arg1']
    result_arg_types = ['Int', '(Array Int Int)']

    def state(self):
        return f'''
(and 
(= {NORMAL_NO_RECURSION} (or (< arg0 0) (> arg0 {self.bound})))
(= is_error (= (select call_result 42) 42))
(= {NORMAL_RECURSION} (and (not {NORMAL_NO_RECURSION}) (not is_error) ))
(= {EXCEPTIONAL} (and (not {NORMAL_NO_RECURSION})  is_error ))

(or 
(and {NORMAL_NO_RECURSION} (= ret arg1) (= ex_status false))
(and 
    {self.recursion_predicate_root_app(
            '(+ 3 arg0)',
            '(store arg1 arg0 (+ arg0 5))',
            'call_result',
            depth='(+ depth 1)',
            ex_status='call_ex_status'
        )}
    (or 
    
    (and 
        {NORMAL_RECURSION}
         (= ret  
             (store
                      call_result
                      (- arg0 1)
                      (+
                        (select call_result arg0)
                        (select call_result (- arg0 1))
                      )
             )
         ) 
         (= ex_status call_ex_status) 
    )
    (and 
        {EXCEPTIONAL}
         (= ex_status true)
    )   
    )
)
)
)
'''
