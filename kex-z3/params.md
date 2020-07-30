#  Global parameters

* auto_config (bool) use heuristics to automatically select solver and configure it (default: true) 
* debug_ref_count (bool) debug support for AST reference counting (default: false) 

* dot_proof_file (string) file in which to output graphical proofs (default: proof.dot) 

* dump_models (bool) dump models whenever check-sat returns sat (default: false) 

* memory_high_watermark (unsigned int) set high watermark for memory consumption (in megabytes), if 0 then there is no limit (default: 0) 

* memory_max_alloc_count (unsigned int) set hard upper limit for memory allocations, if 0 then there is no limit (default: 0) 

* memory_max_size (unsigned int) set hard upper limit for memory consumption (in megabytes), if 0 then there is no limit (default: 0) 

* model (bool) model generation for solvers, this parameter can be overwritten when creating a solver (default: true) 

* model_compress (bool) compress models for easier consumption (default: true) 

* model_validate (bool) validate models produced by solvers (default: false) 

* proof (bool) proof generation, it must be enabled when the Z3 context is created (default: false) 

* rlimit (unsigned int) default resource limit used for solvers. Unrestricted when set to 0. (default: 0) 

* smtlib2_compliant (bool) enable/disable SMT-LIB 2.0 compliance (default: false) 

* stats (bool) enable/disable statistics (default: false) 

* timeout (unsigned int) (default: infty) timeout in milliseconds. (default: 4294967295) 

* trace (bool) trace generation for VCC (default: false) 

* trace_file_name (string) trace out file name (see option 'trace') (default: z3.log) 

* type_check (bool) type checker (alias for well_sorted_check) (default: true) 

* unsat_core (bool) unsat-core generation for solvers, this parameter can be overwritten when creating a solver, not every solver in Z3 supports unsat core generation (default: false) 

* verbose (unsigned int) be verbose, where the value is the verbosity level (default: 0) 

* warning (bool) enable/disable warning messages (default: true) 

* well_sorted_check (bool) type checker (default: false) 


#  pi
###  pattern inference (heuristics) for universal formulas (without annotation)

* arith (unsigned int) 0 - do not infer patterns with arithmetic terms, 1 - use patterns with arithmetic terms if there is no other pattern, 2 - always use patterns with arithmetic terms (default: 1) 

* arith_weight (unsigned int) default weight for quantifiers where the only available pattern has nested arithmetic terms (default: 5) 

* block_loop_patterns (bool) block looping patterns during pattern inference (default: true) 

* max_multi_patterns (unsigned int) when patterns are not provided, the prover uses a heuristic to infer them, this option sets the threshold on the number of extra multi-patterns that can be created; by default, the prover creates at most one multi-pattern when there is no unary pattern (default: 0) 

* non_nested_arith_weight (unsigned int) default weight for quantifiers where the only available pattern has non nested arithmetic terms (default: 10) 

* pull_quantifiers (bool) pull nested quantifiers, if no pattern was found (default: true) 

* use_database (bool) use pattern database (default: false) 

* warnings (bool) enable/disable warning messages in the pattern inference module (default: false) 

#  tactic
###  tactic parameters

* blast_term_ite.max_inflation (unsigned int) multiplicative factor of initial term size. (default: 4294967295) 

* blast_term_ite.max_steps (unsigned int) maximal number of steps allowed for tactic. (default: 4294967295) 

* default_tactic (symbol) overwrite default tactic in strategic solver (default: ) 

* propagate_values.max_rounds (unsigned int) maximal number of rounds to propagate values. (default: 4) 

* solve_eqs.context_solve (bool) solve equalities within disjunctions. (default: true) 

* solve_eqs.ite_solver (bool) use if-then-else solvers. (default: true) 

* solve_eqs.max_occs (unsigned int) maximum number of occurrences for considering a variable for gaussian eliminations. (default: 4294967295) 

* solve_eqs.theory_solver (bool) use theory solvers. (default: true) 

#  pp
###  pretty printer

* bounded (bool) ignore characters exceeding max width (default: false) 

* bv_literals (bool) use Bit-Vector literals (e.g, #x0F and #b0101) during pretty printing (default: true) 

* bv_neg (bool) use bvneg when displaying Bit-Vector literals where the most significant bit is 1 (default: false) 

* decimal (bool) pretty print real numbers using decimal notation (the output may be truncated). Z3 adds a ? if the value is not precise (default: false) 

* decimal_precision (unsigned int) maximum number of decimal places to be used when pp.decimal=true (default: 10) 

* fixed_indent (bool) use a fixed indentation for applications (default: false) 

* flat_assoc (bool) flat associative operators (when pretty printing SMT2 terms/formulas) (default: true) 

* fp_real_literals (bool) use real-numbered floating point literals (e.g, +1.0p-1) during pretty printing (default: false) 

* max_depth (unsigned int) max. term depth (when pretty printing SMT2 terms/formulas) (default: 5) 

* max_indent (unsigned int) max. indentation in pretty printer (default: 4294967295) 

* max_num_lines (unsigned int) max. number of lines to be displayed in pretty printer (default: 4294967295) 

* max_ribbon (unsigned int) max. ribbon (width - indentation) in pretty printer (default: 80) 

* max_width (unsigned int) max. width in pretty printer (default: 80) 

* min_alias_size (unsigned int) min. size for creating an alias for a shared term (when pretty printing SMT2 terms/formulas) (default: 10) 

* pretty_proof (bool) use slower, but prettier, printer for proofs (default: false) 

* simplify_implies (bool) simplify nested implications for pretty printing (default: true) 

* single_line (bool) ignore line breaks when true (default: false) 

#  sat
###  propositional SAT solver

* abce (bool) eliminate blocked clauses using asymmetric literals (default: false) 

* acce (bool) eliminate covered clauses using asymmetric added literals (default: false) 

* asymm_branch (bool) asymmetric branching (default: true) 

* asymm_branch.all (bool) asymmetric branching on all literals per clause (default: false) 

* asymm_branch.delay (unsigned int) number of simplification rounds to wait until invoking asymmetric branch simplification (default: 1) 

* asymm_branch.limit (unsigned int) approx. maximum number of literals visited during asymmetric branching (default: 100000000) 

* asymm_branch.rounds (unsigned int) maximal number of rounds to run asymmetric branch simplifications if progress is made (default: 2) 

* asymm_branch.sampled (bool) use sampling based asymmetric branching based on binary implication graph (default: true) 

* ate (bool) asymmetric tautology elimination (default: true) 

* backtrack.conflicts (unsigned int) number of conflicts before enabling chronological backtracking (default: 4000) 

* backtrack.scopes (unsigned int) number of scopes to enable chronological backtracking (default: 100) 

* bca (bool) blocked clause addition - add blocked binary clauses (default: false) 

* bce (bool) eliminate blocked clauses (default: false) 

* bce_at (unsigned int) eliminate blocked clauses only once at the given simplification round (default: 2) 

* bce_delay (unsigned int) delay eliminate blocked clauses until simplification round (default: 2) 

* binspr (bool) enable SPR inferences of binary propagation redundant clauses. This inprocessing step eliminates models (default: false) 

* blocked_clause_limit (unsigned int) maximum number of literals visited during blocked clause elimination (default: 100000000) 

* branching.anti_exploration (bool) apply anti-exploration heuristic for branch selection (default: false) 

* branching.heuristic (symbol) branching heuristic vsids, lrb or chb (default: vsids) 

* burst_search (unsigned int) number of conflicts before first global simplification (default: 100) 

* cardinality.encoding (symbol) encoding used for at-most-k constraints: grouped, bimander, ordered, unate, circuit (default: grouped) 

* cardinality.solver (bool) use cardinality solver (default: true) 

* cce (bool) eliminate covered clauses (default: false) 

* core.minimize (bool) minimize computed core (default: false) 

* core.minimize_partial (bool) apply partial (cheap) core minimization (default: false) 

* ddfw.init_clause_weight (unsigned int) initial clause weight for DDFW local search (default: 8) 

* ddfw.reinit_base (unsigned int) increment basis for geometric backoff scheme of re-initialization of weights (default: 10000) 

* ddfw.restart_base (unsigned int) number of flips used a starting point for hessitant restart backoff (default: 100000) 

* ddfw.threads (unsigned int) number of ddfw threads to run in parallel with sat solver (default: 0) 

* ddfw.use_reward_pct (unsigned int) percentage to pick highest reward variable when it has reward 0 (default: 15) 

* ddfw_search (bool) use ddfw local search instead of CDCL (default: false) 

* dimacs.core (bool) extract core from DIMACS benchmarks (default: false) 

* drat.activity (bool) dump variable activities (default: false) 

* drat.binary (bool) use Binary DRAT output format (default: false) 

* drat.check_sat (bool) build up internal trace, check satisfying model (default: false) 

* drat.check_unsat (bool) build up internal proof and check (default: false) 

* drat.file (symbol) file to dump DRAT proofs (default: ) 

* dyn_sub_res (bool) dynamic subsumption resolution for minimizing learned clauses (default: true) 

* elim_vars (bool) enable variable elimination using resolution during simplification (default: true) 

* elim_vars_bdd (bool) enable variable elimination using BDD recompilation during simplification (default: true) 

* elim_vars_bdd_delay (unsigned int) delay elimination of variables using BDDs until after simplification round (default: 3) 

* force_cleanup (bool) force cleanup to remove tautologies and simplify clauses (default: false) 

* gc (symbol) garbage collection strategy: psm, glue, glue_psm, dyn_psm (default: glue_psm) 

* gc.burst (bool) perform eager garbage collection during initialization (default: false) 

* gc.defrag (bool) defragment clauses when garbage collecting (default: true) 

* gc.increment (unsigned int) increment to the garbage collection threshold (default: 500) 

* gc.initial (unsigned int) learned clauses garbage collection frequency (default: 20000) 

* gc.k (unsigned int) learned clauses that are inactive for k gc rounds are permanently deleted (only used in dyn_psm) (default: 7) 

* gc.small_lbd (unsigned int) learned clauses with small LBD are never deleted (only used in dyn_psm) (default: 3) 

* inprocess.max (unsigned int) maximal number of inprocessing passes (default: 4294967295) 

* local_search (bool) use local search instead of CDCL (default: false) 

* local_search_dbg_flips (bool) write debug information for number of flips (default: false) 

* local_search_mode (symbol) local search algorithm, either default wsat or qsat (default: wsat) 

* local_search_threads (unsigned int) number of local search threads to find satisfiable solution (default: 0) 

* lookahead.cube.cutoff (symbol) cutoff type used to create lookahead cubes: depth, freevars, psat, adaptive_freevars, adaptive_psat (default: depth) 

* lookahead.cube.depth (unsigned int) cut-off depth to create cubes. Used when lookahead.cube.cutoff is depth. (default: 1) 

* lookahead.cube.fraction (double) adaptive fraction to create lookahead cubes. Used when lookahead.cube.cutoff is adaptive_freevars or adaptive_psat (default: 0.4) 

* lookahead.cube.freevars (double) cube free variable fraction. Used when lookahead.cube.cutoff is freevars (default: 0.8) 

* lookahead.cube.psat.clause_base (double) clause base for PSAT cutoff (default: 2) 

* lookahead.cube.psat.trigger (double) trigger value to create lookahead cubes for PSAT cutoff. Used when lookahead.cube.cutoff is psat (default: 5) 

* lookahead.cube.psat.var_exp (double) free variable exponent for PSAT cutoff (default: 1) 

* lookahead.delta_fraction (double) number between 0 and 1, the smaller the more literals are selected for double lookahead (default: 1.0) 

* lookahead.double (bool) enable doubld lookahead (default: true) 

* lookahead.global_autarky (bool) prefer to branch on variables that occur in clauses that are reduced (default: false) 

* lookahead.preselect (bool) use pre-selection of subset of variables for branching (default: false) 

* lookahead.reward (symbol) select lookahead heuristic: ternary, heule_schur (Heule Schur), heuleu (Heule Unit), unit, or march_cu (default: march_cu) 

* lookahead.use_learned (bool) use learned clauses when selecting lookahead literal (default: false) 

* lookahead_scores (bool) extract lookahead scores. A utility that can only be used from the DIMACS front-end (default: false) 

* lookahead_simplify (bool) use lookahead solver during simplification (default: false) 

* lookahead_simplify.bca (bool) add learned binary clauses as part of lookahead simplification (default: true) 

* max_conflicts (unsigned int) maximum number of conflicts (default: 4294967295) 

* max_memory (unsigned int) maximum amount of memory in megabytes (default: 4294967295) 

* minimize_lemmas (bool) minimize learned clauses (default: true) 

* override_incremental (bool) override incremental safety gaps. Enable elimination of blocked clauses and variables even if solver is reused (default: false) 

* pb.lemma_format (symbol) generate either cardinality or pb lemmas (default: cardinality) 

* pb.min_arity (unsigned int) minimal arity to compile pb/cardinality constraints to CNF (default: 9) 

* pb.resolve (symbol) resolution strategy for boolean algebra solver: cardinality, rounding (default: cardinality) 

* pb.solver (symbol) method for handling Pseudo-Boolean constraints: circuit (arithmetical circuit), sorting (sorting circuit), totalizer (use totalizer encoding), binary_merge, segmented, solver (use native solver) (default: solver) 

* phase (symbol) phase selection strategy: always_false, always_true, basic_caching, random, caching (default: caching) 

* phase.sticky (bool) use sticky phase caching (default: true) 

* prob_search (bool) use probsat local search instead of CDCL (default: false) 

* probing (bool) apply failed literal detection during simplification (default: true) 

* probing_binary (bool) probe binary clauses (default: true) 

* probing_cache (bool) add binary literals as lemmas (default: true) 

* probing_cache_limit (unsigned int) cache binaries unless overall memory usage exceeds cache limit (default: 1024) 

* probing_limit (unsigned int) limit to the number of probe calls (default: 5000000) 

* propagate.prefetch (bool) prefetch watch lists for assigned literals (default: true) 

* random_freq (double) frequency of random case splits (default: 0.01) 

* random_seed (unsigned int) random seed (default: 0) 

* reorder.activity_scale (unsigned int) scaling factor for activity update (default: 100) 

* reorder.base (unsigned int) number of conflicts per random reorder  (default: 4294967295) 

* reorder.itau (double) inverse temperature for softmax (default: 4.0) 

* rephase.base (unsigned int) number of conflicts per rephase  (default: 1000) 

* resolution.cls_cutoff1 (unsigned int) limit1 - total number of problems clauses for the second cutoff of Boolean variable elimination (default: 100000000) 

* resolution.cls_cutoff2 (unsigned int) limit2 - total number of problems clauses for the second cutoff of Boolean variable elimination (default: 700000000) 

* resolution.limit (unsigned int) approx. maximum number of literals visited during variable elimination (default: 500000000) 

* resolution.lit_cutoff_range1 (unsigned int) second cutoff (total number of literals) for Boolean variable elimination, for problems containing less than res_cls_cutoff1 clauses (default: 700) 

* resolution.lit_cutoff_range2 (unsigned int) second cutoff (total number of literals) for Boolean variable elimination, for problems containing more than res_cls_cutoff1 and less than res_cls_cutoff2 (default: 400) 

* resolution.lit_cutoff_range3 (unsigned int) second cutoff (total number of literals) for Boolean variable elimination, for problems containing more than res_cls_cutoff2 (default: 300) 

* resolution.occ_cutoff (unsigned int) first cutoff (on number of positive/negative occurrences) for Boolean variable elimination (default: 10) 

* resolution.occ_cutoff_range1 (unsigned int) second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing less than res_cls_cutoff1 clauses (default: 8) 

* resolution.occ_cutoff_range2 (unsigned int) second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing more than res_cls_cutoff1 and less than res_cls_cutoff2 (default: 5) 

* resolution.occ_cutoff_range3 (unsigned int) second cutoff (number of positive/negative occurrences) for Boolean variable elimination, for problems containing more than res_cls_cutoff2 (default: 3) 

* restart (symbol) restart strategy: static, luby, ema or geometric (default: ema) 

* restart.emafastglue (double) ema alpha factor for fast moving average (default: 0.03) 

* restart.emaslowglue (double) ema alpha factor for slow moving average (default: 1e-05) 

* restart.factor (double) restart increment factor for geometric strategy (default: 1.5) 

* restart.fast (bool) use fast restart approach only removing less active literals. (default: true) 

* restart.initial (unsigned int) initial restart (number of conflicts) (default: 2) 

* restart.margin (double) margin between fast and slow restart factors. For ema (default: 1.1) 

* restart.max (unsigned int) maximal number of restarts. (default: 4294967295) 

* retain_blocked_clauses (bool) retain blocked clauses as lemmas (default: true) 

* scc (bool) eliminate Boolean variables by computing strongly connected components (default: true) 

* scc.tr (bool) apply transitive reduction, eliminate redundant binary clauses (default: true) 

* search.sat.conflicts (unsigned int) period for solving for sat (in number of conflicts) (default: 400) 

* search.unsat.conflicts (unsigned int) period for solving for unsat (in number of conflicts) (default: 400) 

* simplify.delay (unsigned int) set initial delay of simplification by a conflict count (default: 0) 

* subsumption (bool) eliminate subsumed clauses (default: true) 

* subsumption.limit (unsigned int) approx. maximum number of literals visited during subsumption (and subsumption resolution) (default: 100000000) 

* threads (unsigned int) number of parallel threads to use (default: 1) 

* unit_walk (bool) use unit-walk search instead of CDCL (default: false) 

* unit_walk_threads (unsigned int) number of unit-walk search threads to find satisfiable solution (default: 0) 

* variable_decay (unsigned int) multiplier (divided by 100) for the VSIDS activity increment (default: 110) 

* xor.solver (bool) use xor solver (default: false) 

# model

* compact (bool) try to compact function graph (i.e., function interpretations that are lookup tables) (default: false) 

* completion (bool) enable/disable model completion (default: false) 

* inline_def (bool) inline local function definitions ignoring possible expansion (default: false) 

* partial (bool) enable/disable partial function interpretations (default: false) 

* v1 (bool) use Z3 version 1.x pretty printer (default: false) 

* v2 (bool) use Z3 version 2.x (x <= 16) pretty printer (default: false) 

#  solver
###  solver parameters

* cancel_backup_file (symbol) file to save partial search state if search is canceled (default: ) 

* enforce_model_conversion (bool) apply model transformation on new assertions (default: false) 

#  opt
###  optimization parameters

* dump_benchmarks (bool) dump benchmarks for profiling (default: false) 

* dump_models (bool) display intermediary models to stdout (default: false) 

* elim_01 (bool) eliminate 01 variables (default: true) 

* enable_sat (bool) enable the new SAT core for propositional constraints (default: true) 

* enable_sls (bool) enable SLS tuning during weighted maxsast (default: false) 

* maxlex.enable (bool) enable maxlex heuristic for lexicographic MaxSAT problems (default: true) 

* maxres.add_upper_bound_block (bool) restict upper bound with constraint (default: false) 

* maxres.hill_climb (bool) give preference for large weight cores (default: true) 

* maxres.max_core_size (unsigned int) break batch of generated cores if size reaches this number (default: 3) 

* maxres.max_correction_set_size (unsigned int) allow generating correction set constraints up to maximal size (default: 3) 

* maxres.max_num_cores (unsigned int) maximal number of cores per round (default: 4294967295) 

* maxres.maximize_assignment (bool) find an MSS/MCS to improve current assignment (default: false) 

* maxres.pivot_on_correction_set (bool) reduce soft constraints if the current correction set is smaller than current core (default: true) 

* maxres.wmax (bool) use weighted theory solver to constrain upper bounds (default: false) 

* maxsat_engine (symbol) select engine for maxsat: 'core_maxsat', 'wmax', 'maxres', 'pd-maxres' (default: maxres) 

* optsmt_engine (symbol) select optimization engine: 'basic', 'farkas', 'symba' (default: basic) 

* pb.compile_equality (bool) compile arithmetical equalities into pseudo-Boolean equality (instead of two inequalites) (default: false) 

* pp.neat (bool) use neat (as opposed to less readable, but faster) pretty printer when displaying context (default: true) 

* priority (symbol) select how to priortize objectives: 'lex' (lexicographic), 'pareto', 'box' (default: lex) 

* rlimit (unsigned int) resource limit (0 means no limit) (default: 0) 

* solution_prefix (symbol) path prefix to dump intermediary, but non-optimal, solutions (default: ) 

* timeout (unsigned int) timeout (in milliseconds) (UINT_MAX and 0 mean no timeout) (default: 4294967295) 

#  parallel
###  parameters for parallel solver

* conquer.backtrack_frequency (unsigned int) frequency to apply core minimization during conquer (default: 10) 

* conquer.batch_size (unsigned int) number of cubes to batch together for fast conquer (default: 100) 

* conquer.delay (unsigned int) delay of cubes until applying conquer (default: 10) 

* conquer.restart.max (unsigned int) maximal number of restarts during conquer phase (default: 5) 

* enable (bool) enable parallel solver by default on selected tactics (for QF_BV) (default: false) 

* simplify.exp (double) restart and inprocess max is multiplied by simplify.exp ^ depth (default: 1) 

* simplify.inprocess.max (unsigned int) maximal number of inprocessing steps during simplification (default: 2) 

* simplify.max_conflicts (unsigned int) maximal number of conflicts during simplifcation phase (default: 4294967295) 

* simplify.restart.max (unsigned int) maximal number of restarts during simplification phase (default: 5000) 

* threads.max (unsigned int) caps maximal number of threads below the number of processors (default: 10000) 

# lp

* bprop_on_pivoted_rows (bool) propagate bounds on rows changed by the pivot operation (default: true) 

* enable_hnf (bool) enable hnf cuts (default: true) 

* min (bool) minimize cost (default: false) 

* print_stats (bool) print statistic (default: false) 

* rep_freq (unsigned int) the report frequency, in how many iterations print the cost and other info  (default: 0) 

* simplex_strategy (unsigned int) simplex strategy for the solver (default: 0) 

#  nnf
###  negation normal form

* ignore_labels (bool) remove/ignore labels in the input formula, this option is ignored if proofs are enabled (default: false) 

* max_memory (unsigned int) maximum amount of memory in megabytes (default: 4294967295) 

* mode (symbol) NNF translation mode: skolem (skolem normal form), quantifiers (skolem normal form + quantifiers in NNF), full (default: skolem) 

* sk_hack (bool) hack for VCC (default: false) 

#  algebraic
###  real algebraic number package

* factor (bool) use polynomial factorization to simplify polynomials representing algebraic numbers (default: true) 

* factor_max_prime (unsigned int) parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. This parameter limits the maximum prime number p to be used in the first step (default: 31) 

* factor_num_primes (unsigned int) parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. The search space may be reduced by factoring the polynomial in different GF(p)'s. This parameter specify the maximum number of finite factorizations to be considered, before lifiting and searching (default: 1) 

* factor_search_size (unsigned int) parameter for the polynomial factorization procedure in the algebraic number module. Z3 polynomial factorization is composed of three steps: factorization in GF(p), lifting and search. This parameter can be used to limit the search space (default: 5000) 

* min_mag (unsigned int) Z3 represents algebraic numbers using a (square-free) polynomial p and an isolating interval (which contains one and only one root of p). This interval may be refined during the computations. This parameter specifies whether to cache the value of a refined interval or not. It says the minimal size of an interval for caching purposes is 1/2^16 (default: 16) 

* zero_accuracy (unsigned int) one of the most time-consuming operations in the real algebraic number module is determining the sign of a polynomial evaluated at a sample point with non-rational algebraic number values. Let k be the value of this option. If k is 0, Z3 uses precise computation. Otherwise, the result of a polynomial evaluation is considered to be 0 if Z3 can show it is inside the interval (-1/2^k, 1/2^k) (default: 0) 

#  combined_solver
###  combines two solvers: non-incremental (solver1) and incremental (solver2)

* ignore_solver1 (bool) if true, solver 2 is always used (default: false) 

* solver2_timeout (unsigned int) fallback to solver 1 after timeout even when in incremental model (default: 4294967295) 

* solver2_unknown (unsigned int) what should be done when solver 2 returns unknown: 0 - just return unknown, 1 - execute solver 1 if quantifier free problem, 2 - execute solver 1 (default: 1) 

#  rcf
###  real closed fields

* clean_denominators (bool) clean denominators before root isolation (default: true) 

* inf_precision (unsigned int) a value k that is the initial interval size (i.e., (0, 1/2^l)) used as an approximation for infinitesimal values (default: 24) 

* initial_precision (unsigned int) a value k that is the initial interval size (as 1/2^k) when creating transcendentals and approximated division (default: 24) 

* lazy_algebraic_normalization (bool) during sturm-seq and square-free polynomial computations, only normalize algebraic polynomial expressions when the defining polynomial is monic (default: true) 

* max_precision (unsigned int) during sign determination we switch from interval arithmetic to complete methods when the interval size is less than 1/2^k, where k is the max_precision (default: 128) 

* use_prem (bool) use pseudo-remainder instead of remainder when computing GCDs and Sturm-Tarski sequences (default: true) 

# model_evaluator

* array_as_stores (bool) return array as a set of stores (default: true) 

* array_equalities (bool) evaluate array equalities (default: true) 

* completion (bool) assigns an interptetation to symbols that do not have one in the current model, when evaluating expressions in the current model (default: false) 

* max_memory (unsigned int) maximum amount of memory in megabytes (default: 4294967295) 

* max_steps (unsigned int) maximum number of steps (default: 4294967295) 

#  ackermannization
###  tactics based on solving UF-theories via ackermannization (see also ackr module)

* eager (bool) eagerly instantiate all congruence rules (default: true) 

* inc_sat_backend (bool) use incremental SAT (default: false) 

* sat_backend (bool) use SAT rather than SMT in qfufbv_ackr_tactic (default: false) 

#  nlsat
###  nonlinear solver

* factor (bool) factor polynomials produced during conflict resolution. (default: true) 

* inline_vars (bool) inline variables that can be isolated from equations (default: false) 

* lazy (unsigned int) how lazy the solver is. (default: 0) 

* log_lemmas (bool) display lemmas as self-contained SMT formulas (default: false) 

* max_conflicts (unsigned int) maximum number of conflicts. (default: 4294967295) 

* max_memory (unsigned int) maximum amount of memory in megabytes (default: 4294967295) 

* minimize_conflicts (bool) minimize conflicts (default: false) 

* randomize (bool) randomize selection of a witness in nlsat. (default: true) 

* reorder (bool) reorder variables. (default: true) 

* seed (unsigned int) random seed. (default: 0) 

* shuffle_vars (bool) use a random variable order. (default: false) 

* simplify_conflicts (bool) simplify conflicts using equalities before resolving them in nlsat solver. (default: true) 

#  parser

* error_for_visual_studio (bool) display error messages in Visual Studio format (default: false) 

* ignore_bad_patterns (bool) ignore malformed patterns (default: true) 

* ignore_user_patterns (bool) ignore patterns provided by the user (default: false) 

#  rewriter
###  new formula simplification module used in the tactic framework, and new solvers

* algebraic_number_evaluator (bool) simplify/evaluate expressions containing (algebraic) irrational numbers. (default: true) 

* arith_ineq_lhs (bool) rewrite inequalities so that right-hand-side is a constant. (default: false) 

* arith_lhs (bool) all monomials are moved to the left-hand-side, and the right-hand-side is just a constant. (default: false) 

* bit2bool (bool) try to convert bit-vector terms of size 1 into Boolean terms (default: true) 

* blast_distinct (bool) expand a distinct predicate into a quadratic number of disequalities (default: false) 

* blast_distinct_threshold (unsigned int) when blast_distinct is true, only distinct expressions with less than this number of arguments are blasted (default: 4294967295) 

* blast_eq_value (bool) blast (some) Bit-vector equalities into bits (default: false) 

* bv_extract_prop (bool) attempt to partially propagate extraction inwards (default: false) 

* bv_ineq_consistency_test_max (unsigned int) max size of conjunctions on which to perform consistency test based on inequalities on bitvectors. (default: 0) 

* bv_ite2id (bool) rewrite ite that can be simplified to identity (default: false) 

* bv_le_extra (bool) additional bu_(u/s)le simplifications (default: false) 

* bv_not_simpl (bool) apply simplifications for bvnot (default: false) 

* bv_sort_ac (bool) sort the arguments of all AC operators (default: false) 

* bv_trailing (bool) lean removal of trailing zeros (default: false) 

* bv_urem_simpl (bool) additional simplification for bvurem (default: false) 

* bvnot2arith (bool) replace (bvnot x) with (bvsub -1 x) (default: false) 

* cache_all (bool) cache all intermediate results. (default: false) 

* div0_ackermann_limit (unsigned int) a bound for number of congruence Ackermann lemmas for div0 modelling (default: 1000) 

* elim_and (bool) conjunctions are rewritten using negation and disjunctions (default: false) 

* elim_ite (bool) eliminate ite in favor of and/or (default: true) 

* elim_rem (bool) replace (rem x y) with (ite (>= y 0) (mod x y) (- (mod x y))). (default: false) 

* elim_sign_ext (bool) expand sign-ext operator using concat and extract (default: true) 

* elim_to_real (bool) eliminate to_real from arithmetic predicates that contain only integers. (default: false) 

* eq2ineq (bool) expand equalities into two inequalities (default: false) 

* expand_power (bool) expand (^ t k) into (* t ... t) if  1 < k <= max_degree. (default: false) 

* expand_select_store (bool) replace a (select (store ...) ...) term by an if-then-else term (default: false) 

* expand_store_eq (bool) reduce (store ...) = (store ...) with a common base into selects (default: false) 

* expand_tan (bool) replace (tan x) with (/ (sin x) (cos x)). (default: false) 

* flat (bool) create nary applications for and,or,+,*,bvadd,bvmul,bvand,bvor,bvxor (default: true) 

* gcd_rounding (bool) use gcd rounding on integer arithmetic atoms. (default: false) 

* hi_div0 (bool) use the 'hardware interpretation' for division by zero (for bit-vector terms) (default: true) 

* hi_fp_unspecified (bool) use the 'hardware interpretation' for unspecified values in fp.min, fp.max, fp.to_ubv, fp.to_sbv, and fp.to_real (default: false) 

* hoist_cmul (bool) hoist constant multiplication over summation to minimize number of multiplications (default: false) 

* hoist_ite (bool) hoist shared summands under ite expressions (default: false) 

* hoist_mul (bool) hoist multiplication over summation to minimize number of multiplications (default: false) 

* ignore_patterns_on_ground_qbody (bool) ignores patterns on quantifiers that don't mention their bound variables. (default: true) 

* ite_extra_rules (bool) extra ite simplifications, these additional simplifications may reduce size locally but increase globally (default: false) 

* local_ctx (bool) perform local (i.e., cheap) context simplifications (default: false) 

* local_ctx_limit (unsigned int) limit for applying local context simplifier (default: 4294967295) 

* max_degree (unsigned int) max degree of algebraic numbers (and power operators) processed by simplifier. (default: 64) 

* max_memory (unsigned int) maximum amount of memory in megabytes (default: 4294967295) 

* max_steps (unsigned int) maximum number of steps (default: 4294967295) 

* mul2concat (bool) replace multiplication by a power of two into a concatenation (default: false) 

* mul_to_power (bool) collpase (* t ... t) into (^ t k), it is ignored if expand_power is true. (default: false) 

* pull_cheap_ite (bool) pull if-then-else terms when cheap. (default: false) 

* push_ite_arith (bool) push if-then-else over arithmetic terms. (default: false) 

* push_ite_bv (bool) push if-then-else over bit-vector terms. (default: false) 

* push_to_real (bool) distribute to_real over * and +. (default: true) 

* rewrite_patterns (bool) rewrite patterns. (default: false) 

* som (bool) put polynomials in som-of-monomials form (default: false) 

* som_blowup (unsigned int) maximum increase of monomials generated when putting a polynomial in sum-of-monomials normal form (default: 10) 

* sort_store (bool) sort nested stores when the indices are known to be different (default: false) 

* sort_sums (bool) sort the arguments of + application. (default: false) 

* split_concat_eq (bool) split equalities of the form (= (concat t1 t2) t3) (default: false) 

* udiv2mul (bool) convert constant udiv to mul (default: false) 

#  fp
###  fixedpoint parameters

* bmc.linear_unrolling_depth (unsigned int) Maximal level to explore (default: 4294967295) 

* datalog.all_or_nothing_deltas (bool) compile rules so that it is enough for the delta relation in union and widening operations to determine only whether the updated relation was modified or not (default: false) 

* datalog.check_relation (symbol) name of default relation to check. operations on the default relation will be verified using SMT solving (default: null) 

* datalog.compile_with_widening (bool) widening will be used to compile recursive rules (default: false) 

* datalog.dbg_fpr_nonempty_relation_signature (bool) if true, finite_product_relation will attempt to avoid creating inner relation with empty signature by putting in half of the table columns, if it would have been empty otherwise (default: false) 

* datalog.default_relation (symbol) default relation implementation: external_relation, pentagon (default: pentagon) 

* datalog.default_table (symbol) default table implementation: sparse, hashtable, bitvector, interval (default: sparse) 

* datalog.default_table_checked (bool) if true, the default table will be default_table inside a wrapper that checks that its results are the same as of default_table_checker table (default: false) 

* datalog.default_table_checker (symbol) see default_table_checked (default: null) 

* datalog.explanations_on_relation_level (bool) if true, explanations are generated as history of each relation, rather than per fact (generate_explanations must be set to true for this option to have any effect) (default: false) 

* datalog.generate_explanations (bool) produce explanations for produced facts when using the datalog engine (default: false) 

* datalog.initial_restart_timeout (unsigned int) length of saturation run before the first restart (in ms), zero means no restarts (default: 0) 

* datalog.magic_sets_for_queries (bool) magic set transformation will be used for queries (default: false) 

* datalog.output_profile (bool) determines whether profile information should be output when outputting Datalog rules or instructions (default: false) 

* datalog.print.tuples (bool) determines whether tuples for output predicates should be output (default: true) 

* datalog.profile_timeout_milliseconds (unsigned int) instructions and rules that took less than the threshold will not be printed when printed the instruction/rule list (default: 0) 

* datalog.similarity_compressor (bool) rules that differ only in values of constants will be merged into a single rule (default: true) 

* datalog.similarity_compressor_threshold (unsigned int) if similarity_compressor is on, this value determines how many similar rules there must be in order for them to be merged (default: 11) 

* datalog.subsumption (bool) if true, removes/filters predicates with total transitions (default: true) 

* datalog.timeout (unsigned int) Time limit used for saturation (default: 0) 

* datalog.unbound_compressor (bool) auxiliary relations will be introduced to avoid unbound variables in rule heads (default: true) 

* datalog.use_map_names (bool) use names from map files when displaying tuples (default: true) 

* engine (symbol) Select: auto-config, datalog, bmc, spacer (default: auto-config) 

* generate_proof_trace (bool) trace for 'sat' answer as proof object (default: false) 

* print_aig (symbol) Dump clauses in AIG text format (AAG) to the given file name (default: ) 

* print_answer (bool) print answer instance(s) to query (default: false) 

* print_boogie_certificate (bool) print certificate for reachability or non-reachability using a format understood by Boogie (default: false) 

* print_certificate (bool) print certificate for reachability or non-reachability (default: false) 

* print_fixedpoint_extensions (bool) use SMT-LIB2 fixedpoint extensions, instead of pure SMT2, when printing rules (default: true) 

* print_low_level_smt2 (bool) use (faster) low-level SMT2 printer (the printer is scalable but the result may not be as readable) (default: false) 

* print_statistics (bool) print statistics (default: false) 

* print_with_variable_declarations (bool) use variable declarations when displaying rules (instead of attempting to use original names) (default: true) 

* spacer.blast_term_ite_inflation (unsigned int) Maximum inflation for non-Boolean ite-terms expansion: 0 (none), k (multiplicative) (default: 3) 

* spacer.ctp (bool) Enable counterexample-to-pushing (default: true) 

* spacer.dump_benchmarks (bool) Dump SMT queries as benchmarks (default: false) 

* spacer.dump_threshold (double) Threshold in seconds on dumping benchmarks (default: 5.0) 

* spacer.elim_aux (bool) Eliminate auxiliary variables in reachability facts (default: true) 

* spacer.eq_prop (bool) Enable equality and bound propagation in arithmetic (default: true) 

* spacer.gpdr (bool) Use GPDR solving strategy for non-linear CHC (default: false) 

* spacer.gpdr.bfs (bool) Use BFS exploration strategy for expanding model search (default: true) 

* spacer.ground_pobs (bool) Ground pobs by using values from a model (default: true) 

* spacer.iuc (unsigned int) 0 = use old implementation of unsat-core-generation, 1 = use new implementation of IUC generation, 2 = use new implementation of IUC + min-cut optimization (default: 1) 

* spacer.iuc.arith (unsigned int) 0 = use simple Farkas plugin, 1 = use simple Farkas plugin with constant from other partition (like old unsat-core-generation),2 = use Gaussian elimination optimization (broken), 3 = use additive IUC plugin (default: 1) 

* spacer.iuc.debug_proof (bool) prints proof used by unsat-core-learner for debugging purposes (debugging) (default: false) 

* spacer.iuc.old_hyp_reducer (bool) use old hyp reducer instead of new implementation, for debugging only (default: false) 

* spacer.iuc.print_farkas_stats (bool) prints for each proof how many Farkas lemmas it contains and how many of these participate in the cut (for debugging) (default: false) 

* spacer.iuc.split_farkas_literals (bool) Split Farkas literals (default: false) 

* spacer.keep_proxy (bool) keep proxy variables (internal parameter) (default: true) 

* spacer.max_level (unsigned int) Maximum level to explore (default: 4294967295) 

* spacer.max_num_contexts (unsigned int) maximal number of contexts to create (default: 500) 

* spacer.mbqi (bool) Enable mbqi (default: true) 

* spacer.min_level (unsigned int) Minimal level to explore (default: 0) 

* spacer.native_mbp (bool) Use native mbp of Z3 (default: true) 

* spacer.order_children (unsigned int) SPACER: order of enqueuing children in non-linear rules : 0 (original), 1 (reverse), 2 (random) (default: 0) 

* spacer.p3.share_invariants (bool) Share invariants lemmas (default: false) 

* spacer.p3.share_lemmas (bool) Share frame lemmas (default: false) 

* spacer.print_json (symbol) Print pobs tree in JSON format to a given file (default: ) 

* spacer.propagate (bool) Enable propagate/pushing phase (default: true) 

* spacer.push_pob (bool) push blocked pobs to higher level (default: false) 

* spacer.push_pob_max_depth (unsigned int) Maximum depth at which push_pob is enabled (default: 4294967295) 

* spacer.q3 (bool) Allow quantified lemmas in frames (default: true) 

* spacer.q3.instantiate (bool) Instantiate quantified lemmas (default: true) 

* spacer.q3.qgen.normalize (bool) normalize cube before quantified generalization (default: true) 

* spacer.q3.use_qgen (bool) use quantified lemma generalizer (default: false) 

* spacer.random_seed (unsigned int) Random seed to be used by SMT solver (default: 0) 

* spacer.reach_dnf (bool) Restrict reachability facts to DNF (default: true) 

* spacer.reset_pob_queue (bool) SPACER: reset pob obligation queue when entering a new level (default: true) 

* spacer.restart_initial_threshold (unsigned int) Initial threshold for restarts (default: 10) 

* spacer.restarts (bool) Enable resetting obligation queue (default: false) 

* spacer.simplify_lemmas_post (bool) simplify derived lemmas after inductive propagation (default: false) 

* spacer.simplify_lemmas_pre (bool) simplify derived lemmas before inductive propagation (default: false) 

* spacer.simplify_pob (bool) simplify pobs by removing redundant constraints (default: false) 

* spacer.use_array_eq_generalizer (bool) SPACER: attempt to generalize lemmas with array equalities (default: true) 

* spacer.use_bg_invs (bool) Enable external background invariants (default: false) 

* spacer.use_derivations (bool) SPACER: using derivation mechanism to cache intermediate results for non-linear rules (default: true) 

* spacer.use_euf_gen (bool) Generalize lemmas and pobs using implied equalities (default: false) 

* spacer.use_inc_clause (bool) Use incremental clause to represent trans (default: true) 

* spacer.use_inductive_generalizer (bool) generalize lemmas using induction strengthening (default: true) 

* spacer.use_lemma_as_cti (bool) SPACER: use a lemma instead of a CTI in flexible_trace (default: false) 

* spacer.use_lim_num_gen (bool) Enable limit numbers generalizer to get smaller numbers (default: false) 

* spacer.validate_lemmas (bool) Validate each lemma after generalization (default: false) 

* spacer.weak_abs (bool) Weak abstraction (default: true) 

* tab.selection (symbol) selection method for tabular strategy: weight (default), first, var-use (default: weight) 

* validate (bool) validate result (by proof checking or model checking) (default: false) 

* xform.array_blast (bool) try to eliminate local array terms using Ackermannization -- some array terms may remain (default: false) 

* xform.array_blast_full (bool) eliminate all local array variables by QE (default: false) 

* xform.bit_blast (bool) bit-blast bit-vectors (default: false) 

* xform.coalesce_rules (bool) coalesce rules (default: false) 

* xform.coi (bool) use cone of influence simplification (default: true) 

* xform.compress_unbound (bool) compress tails with unbound variables (default: true) 

* xform.elim_term_ite (bool) Eliminate term-ite expressions (default: false) 

* xform.elim_term_ite.inflation (unsigned int) Maximum inflation for non-Boolean ite-terms blasting: 0 (none), k (multiplicative) (default: 3) 

* xform.fix_unbound_vars (bool) fix unbound variables in tail (default: false) 

* xform.inline_eager (bool) try eager inlining of rules (default: true) 

* xform.inline_linear (bool) try linear inlining method (default: true) 

* xform.inline_linear_branch (bool) try linear inlining method with potential expansion (default: false) 

* xform.instantiate_arrays (bool) Transforms P(a) into P(i, a[i] a) (default: false) 

* xform.instantiate_arrays.enforce (bool) Transforms P(a) into P(i, a[i]), discards a from predicate (default: false) 

* xform.instantiate_arrays.nb_quantifier (unsigned int) Gives the number of quantifiers per array (default: 1) 

* xform.instantiate_arrays.slice_technique (symbol) <no-slicing>=> GetId(i) = i, <smash> => GetId(i) = true (default: no-slicing) 

* xform.instantiate_quantifiers (bool) instantiate quantified Horn clauses using E-matching heuristic (default: false) 

* xform.karr (bool) Add linear invariants to clauses using Karr's method (default: false) 

* xform.magic (bool) perform symbolic magic set transformation (default: false) 

* xform.quantify_arrays (bool) create quantified Horn clauses from clauses with arrays (default: false) 

* xform.scale (bool) add scaling variable to linear real arithmetic clauses (default: false) 

* xform.slice (bool) simplify clause set using slicing (default: true) 

* xform.subsumption_checker (bool) Enable subsumption checker (no support for model conversion) (default: true) 

* xform.tail_simplifier_pve (bool) propagate_variable_equivalences (default: true) 

* xform.transform_arrays (bool) Rewrites arrays equalities and applies select over store (default: false) 

* xform.unfold_rules (unsigned int) unfold rules statically using iterative squaring (default: 0) 

#  smt
###  smt solver based on lazy smt

* arith.auto_config_simplex (bool) force simplex solver in auto_config (default: false) 

* arith.branch_cut_ratio (unsigned int) branch/cut ratio for linear integer arithmetic (default: 2) 

* arith.dump_lemmas (bool) dump arithmetic theory lemmas to files (default: false) 

* arith.eager_eq_axioms (bool) eager equality axioms (default: true) 

* arith.euclidean_solver (bool) eucliean solver for linear integer arithmetic (default: false) 

* arith.greatest_error_pivot (bool) Pivoting strategy (default: false) 

* arith.ignore_int (bool) treat integer variables as real (default: false) 

* arith.int_eq_branch (bool) branching using derived integer equations (default: false) 

* arith.nl (bool) (incomplete) nonlinear arithmetic support based on Groebner basis and interval propagation (default: true) 

* arith.nl.branching (bool) branching on integer variables in non linear clusters (default: true) 

* arith.nl.gb (bool) groebner Basis computation, this option is ignored when arith.nl=false (default: true) 

* arith.nl.rounds (unsigned int) threshold for number of (nested) final checks for non linear arithmetic (default: 1024) 

* arith.propagate_eqs (bool) propagate (cheap) equalities (default: true) 

* arith.propagation_mode (unsigned int) 0 - no propagation, 1 - propagate existing literals, 2 - refine bounds (default: 2) 

* arith.random_initial_value (bool) use random initial values in the simplex-based procedure for linear arithmetic (default: false) 

* arith.reflect (bool) reflect arithmetical operators to the congruence closure (default: true) 

* arith.solver (unsigned int) arithmetic solver: 0 - no solver, 1 - bellman-ford based solver (diff. logic only), 2 - simplex based solver, 3 - floyd-warshall based solver (diff. logic only) and no theory combination 4 - utvpi, 5 - infinitary lra, 6 - lra solver (default: 2) 

* array.extensional (bool) extensional array theory (default: true) 

* array.weak (bool) weak array theory (default: false) 

* auto_config (bool) automatically configure solver (default: true) 

* bv.enable_int2bv (bool) enable support for int2bv and bv2int operators (default: true) 

* bv.reflect (bool) create enode for every bit-vector term (default: true) 

* case_split (unsigned int) 0 - case split based on variable activity, 1 - similar to 0, but delay case splits created during the search, 2 - similar to 0, but cache the relevancy, 3 - case split based on relevancy (structural splitting), 4 - case split on relevancy and activity, 5 - case split on relevancy and current goal, 6 - activity-based case split with theory-aware branching activity (default: 1) 

* clause_proof (bool) record a clausal proof (default: false) 

* core.extend_nonlocal_patterns (bool) extend unsat cores with literals that have quantifiers with patterns that contain symbols which are not in the quantifier's body (default: false) 

* core.extend_patterns (bool) extend unsat core with literals that trigger (potential) quantifier instances (default: false) 

* core.extend_patterns.max_distance (unsigned int) limits the distance of a pattern-extended unsat core (default: 4294967295) 

* core.minimize (bool) minimize unsat core produced by SMT context (default: false) 

* core.validate (bool) validate unsat core produced by SMT context (default: false) 

* dack (unsigned int) 0 - disable dynamic ackermannization, 1 - expand Leibniz's axiom if a congruence is the root of a conflict, 2 - expand Leibniz's axiom if a congruence is used during conflict resolution (default: 1) 

* dack.eq (bool) enable dynamic ackermannization for transtivity of equalities (default: false) 

* dack.factor (double) number of instance per conflict (default: 0.1) 

* dack.gc (unsigned int) Dynamic ackermannization garbage collection frequency (per conflict) (default: 2000) 

* dack.gc_inv_decay (double) Dynamic ackermannization garbage collection decay (default: 0.8) 

* dack.threshold (unsigned int)  number of times the congruence rule must be used before Leibniz's axiom is expanded (default: 10) 

* delay_units (bool) if true then z3 will not restart when a unit clause is learned (default: false) 

* delay_units_threshold (unsigned int) maximum number of learned unit clauses before restarting, ignored if delay_units is false (default: 32) 

* dt_lazy_splits (unsigned int) How lazy datatype splits are performed: 0- eager, 1- lazy for infinite types, 2- lazy (default: 1) 

* ematching (bool) E-Matching based quantifier instantiation (default: true) 

* lemma_gc_strategy (unsigned int) lemma garbage collection strategy: 0 - fixed, 1 - geometric, 2 - at restart, 3 - none (default: 0) 

* logic (symbol) logic used to setup the SMT solver (default: ) 

* macro_finder (bool) try to find universally quantified formulas that can be viewed as macros (default: false) 

* max_conflicts (unsigned int) maximum number of conflicts before giving up. (default: 4294967295) 

* mbqi (bool) model based quantifier instantiation (MBQI) (default: true) 

* mbqi.force_template (unsigned int) some quantifiers can be used as templates for building interpretations for functions. Z3 uses heuristics to decide whether a quantifier will be used as a template or not. Quantifiers with weight >= mbqi.force_template are forced to be used as a template (default: 10) 

* mbqi.id (string) Only use model-based instantiation for quantifiers with id's beginning with string (default: ) 

* mbqi.max_cexs (unsigned int) initial maximal number of counterexamples used in MBQI, each counterexample generates a quantifier instantiation (default: 1) 

* mbqi.max_cexs_incr (unsigned int) increment for MBQI_MAX_CEXS, the increment is performed after each round of MBQI (default: 0) 

* mbqi.max_iterations (unsigned int) maximum number of rounds of MBQI (default: 1000) 

* mbqi.trace (bool) generate tracing messages for Model Based Quantifier Instantiation (MBQI). It will display a message before every round of MBQI, and the quantifiers that were not satisfied (default: false) 

* pb.conflict_frequency (unsigned int) conflict frequency for Pseudo-Boolean theory (default: 1000) 

* pb.learn_complements (bool) learn complement literals for Pseudo-Boolean theory (default: true) 

* phase_selection (unsigned int) phase selection heuristic: 0 - always false, 1 - always true, 2 - phase caching, 3 - phase caching conservative, 4 - phase caching conservative 2, 5 - random, 6 - number of occurrences, 7 - theory (default: 3) 

* pull_nested_quantifiers (bool) pull nested quantifiers (default: false) 

* qi.cost (string) expression specifying what is the cost of a given quantifier instantiation (default: (+ weight generation)) 

* qi.eager_threshold (double) threshold for eager quantifier instantiation (default: 10.0) 

* qi.lazy_threshold (double) threshold for lazy quantifier instantiation (default: 20.0) 

* qi.max_instances (unsigned int) maximum number of quantifier instantiations (default: 4294967295) 

* qi.max_multi_patterns (unsigned int) specify the number of extra multi patterns (default: 0) 

* qi.profile (bool) profile quantifier instantiation (default: false) 

* qi.profile_freq (unsigned int) how frequent results are reported by qi.profile (default: 4294967295) 

* qi.quick_checker (unsigned int) specify quick checker mode, 0 - no quick checker, 1 - using unsat instances, 2 - using both unsat and no-sat instances (default: 0) 

* quasi_macros (bool) try to find universally quantified formulas that are quasi-macros (default: false) 

* random_seed (unsigned int) random seed for the smt solver (default: 0) 

* recfun.depth (unsigned int) initial depth for maxrec expansion (default: 2) 

* recfun.native (bool) use native rec-fun solver (default: true) 

* refine_inj_axioms (bool) refine injectivity axioms (default: true) 

* relevancy (unsigned int) relevancy propagation heuristic: 0 - disabled, 1 - relevancy is tracked by only affects quantifier instantiation, 2 - relevancy is tracked, and an atom is only asserted if it is relevant (default: 2) 

* restart.max (unsigned int) maximal number of restarts. (default: 4294967295) 

* restart_factor (double) when using geometric (or inner-outer-geometric) progression of restarts, it specifies the constant used to multiply the current restart threshold (default: 1.1) 

* restart_strategy (unsigned int) 0 - geometric, 1 - inner-outer-geometric, 2 - luby, 3 - fixed, 4 - arithmetic (default: 1) 

* restricted_quasi_macros (bool) try to find universally quantified formulas that are restricted quasi-macros (default: false) 

* seq.split_w_len (bool) enable splitting guided by length constraints (default: true) 

* str.aggressive_length_testing (bool) prioritize testing concrete length values over generating more options (default: false) 

* str.aggressive_unroll_testing (bool) prioritize testing concrete regex unroll counts over generating more options (default: true) 

* str.aggressive_value_testing (bool) prioritize testing concrete string constant values over generating more options (default: false) 

* str.binary_search_start (unsigned int) initial upper bound for theory_str binary search (default: 64) 

* str.fast_length_tester_cache (bool) cache length tester constants instead of regenerating them (default: false) 

* str.fast_value_tester_cache (bool) cache value tester constants instead of regenerating them (default: true) 

* str.finite_overlap_models (bool) attempt a finite model search for overlapping variables instead of completely giving up on the arrangement (default: false) 

* str.overlap_priority (double) theory-aware priority for overlapping variable cases; use smt.theory_aware_branching=true (default: -0.1) 

* str.regex_automata (bool) use automata-based reasoning for regular expressions (Z3str3 only) (default: true) 

* str.regex_automata_difficulty_threshold (unsigned int) difficulty threshold for regex automata heuristics (default: 1000) 

* str.regex_automata_failed_automaton_threshold (unsigned int) number of failed automaton construction attempts after which a full automaton is automatically built (default: 10) 

* str.regex_automata_failed_intersection_threshold (unsigned int) number of failed automaton intersection attempts after which intersection is always computed (default: 10) 

* str.regex_automata_intersection_difficulty_threshold (unsigned int) difficulty threshold for regex intersection heuristics (default: 1000) 

* str.regex_automata_length_attempt_threshold (unsigned int) number of length/path constraint attempts before checking unsatisfiability of regex terms (default: 10) 

* str.string_constant_cache (bool) cache all generated string constants generated from anywhere in theory_str (default: true) 

* str.strong_arrangements (bool) assert equivalences instead of implications when generating string arrangement axioms (default: true) 

* str.use_binary_search (bool) use a binary search heuristic for finding concrete length values for free variables in theory_str (set to False to use linear search) (default: false) 

* string_solver (symbol) solver for string/sequence theories. options are: 'z3str3' (specialized string solver), 'seq' (sequence solver), 'auto' (use static features to choose best solver), 'empty' (a no-op solver that forces an answer unknown if strings were used), 'none' (no solver) (default: seq) 

* theory_aware_branching (bool) Allow the context to use extra information from theory solvers regarding literal branching prioritization. (default: false) 

* theory_case_split (bool) Allow the context to use heuristics involving theory case splits, which are a set of literals of which exactly one can be assigned True. If this option is false, the context will generate extra axioms to enforce this instead. (default: false) 

#  sls
###  Experimental Stochastic Local Search Solver (for QFBV only).

* early_prune (bool) use early pruning for score prediction (default: true) 

* max_memory (unsigned int) maximum amount of memory in megabytes (default: 4294967295) 

* max_restarts (unsigned int) maximum number of restarts (default: 4294967295) 

* paws_init (unsigned int) initial/minimum assertion weights (default: 40) 

* paws_sp (unsigned int) smooth assertion weights with probability paws_sp / 1024 (default: 52) 

* random_offset (bool) use random offset for candidate evaluation (default: true) 

* random_seed (unsigned int) random seed (default: 0) 

* rescore (bool) rescore/normalize top-level score every base restart interval (default: true) 

* restart_base (unsigned int) base restart interval given by moves per run (default: 100) 

* restart_init (bool) initialize to 0 or random value (= 1) after restart (default: false) 

* scale_unsat (double) scale score of unsat expressions by this factor (default: 0.5) 

* track_unsat (bool) keep a list of unsat assertions as done in SAT - currently disabled internally (default: false) 

* vns_mc (unsigned int) in local minima, try Monte Carlo sampling vns_mc many 2-bit-flips per bit (default: 0) 

* vns_repick (bool) in local minima, try picking a different assertion (only for walksat) (default: false) 

* walksat (bool) use walksat assertion selection (instead of gsat) (default: true) 

* walksat_repick (bool) repick assertion if randomizing in local minima (default: true) 

* walksat_ucb (bool) use bandit heuristic for walksat assertion selection (instead of random) (default: true) 

* walksat_ucb_constant (double) the ucb constant c in the term score + c * f(touched) (default: 20.0) 

* walksat_ucb_forget (double) scale touched by this factor every base restart interval (default: 1.0) 

* walksat_ucb_init (bool) initialize total ucb touched to formula size (default: false) 

* walksat_ucb_noise (double) add noise 0 <= 256 * ucb_noise to ucb score for assertion selection (default: 0.0002) 

* wp (unsigned int) random walk with probability wp / 1024 (default: 100) 


#  simplify

* ite_extra_rules: extra ite simplifications, these additional simplifications may reduce size locally but increase globally 

* flat: create nary applications for and,or,+,*,bvadd,bvmul,bvand,bvor,bvxor

* elim_and: conjunctions are rewritten using negation and disjunctions

* elim_ite: eliminate ite in favor of and/or

* local_ctx: perform local (i.e., cheap) context simplifications

* local_ctx_limit: limit for applying local context simplifier

* blast_distinct: expand a distinct predicate into a quadratic number of disequalities

* blast_distinct_threshold: when blast_distinct is true, only distinct expressions with less than this number of arguments are blasted

* som: put polynomials in som-of-monomials form

* som_blowup: maximum increase of monomials generated when putting a polynomial in sum-of-monomials normal form

* hoist_mul: hoist multiplication over summation to minimize number of multiplications

* hoist_cmul: hoist constant multiplication over summation to minimize number of multiplications

* hoist_ite: hoist shared summands under ite expressions

* algebraic_number_evaluator: simplify/evaluate expressions containing (algebraic) irrational numbers.

* mul_to_power: collpase (* t ... t) into (^ t k), it is ignored if expand_power is true.

* expand_power: expand (^ t k) into (* t ... t) if  1 < k <= max_degree.

* expand_tan: replace (tan x) with (/ (sin x) (cos x)).

* max_degree: max degree of algebraic numbers (and power operators) processed by simplifier.

* sort_sums: sort the arguments of + application.

* gcd_rounding: use gcd rounding on integer arithmetic atoms.

* arith_lhs: all monomials are moved to the left-hand-side, and the right-hand-side is just a constant.

* arith_ineq_lhs: rewrite inequalities so that right-hand-side is a constant.

* elim_to_real: eliminate to_real from arithmetic predicates that contain only integers.

* push_to_real: distribute to_real over * and +.

* eq2ineq: expand equalities into two inequalities

* elim_rem: replace (rem x y) with (ite (>= y 0) (mod x y) (- (mod x y))).

* udiv2mul: convert constant udiv to mul

* split_concat_eq: split equalities of the form (= (concat t1 t2) t3)

* bit2bool: try to convert bit-vector terms of size 1 into Boolean terms

* blast_eq_value: blast (some) Bit-vector equalities into bits

* elim_sign_ext: expand sign-ext operator using concat and extract

* hi_div0: use the 'hardware interpretation' for division by zero (for bit-vector terms)

* mul2concat: replace multiplication by a power of two into a concatenation

* bvnot2arith: replace (bvnot x) with (bvsub -1 x)

* bv_sort_ac: sort the arguments of all AC operators

* bv_trailing: lean removal of trailing zeros

* bv_extract_prop: attempt to partially propagate extraction inwards

* bv_not_simpl: apply simplifications for bvnot

* bv_ite2id: rewrite ite that can be simplified to identity

* bv_le_extra: additional bu_(u/s)le simplifications

* bv_urem_simpl: additional simplification for bvurem

* expand_select_store: replace a (select (store ...) ...) term by an if-then-else term

* expand_store_eq: reduce (store ...) = (store ...) with a common base into selects

* sort_store: sort nested stores when the indices are known to be different

* max_memory: maximum amount of memory in megabytes

* max_steps: maximum number of steps

* push_ite_arith: push if-then-else over arithmetic terms.

* push_ite_bv: push if-then-else over bit-vector terms.

* pull_cheap_ite: pull if-then-else terms when cheap.

* bv_ineq_consistency_test_max: max size of conjunctions on which to perform consistency test based on inequalities on bitvectors.

* cache_all: cache all intermediate results.

* rewrite_patterns: rewrite patterns.

* ignore_patterns_on_ground_qbody: ignores patterns on quantifiers that don't mention their bound variables.

