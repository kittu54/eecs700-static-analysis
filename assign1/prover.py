from z3 import *
from parser import py_ast, WhilePyVisitor
import sys
import pprint
# --- Global State ---
PROC_ENV = {}
ALL_VARS = set()
FRESH_COUNTER = 0
Z3_FUNC_CACHE = {}

def next_fresh_id():
    """Generates a unique ID for fresh variables."""
    global FRESH_COUNTER
    FRESH_COUNTER += 1
    return FRESH_COUNTER

def find_old_vars(expr_ast):
    """Recursively finds all 'old(v)' variable names in an AST node."""
    vars = set()
    if isinstance(expr_ast, list):
        if expr_ast[0] == 'old':
            vars.add(expr_ast[1])
        else:
            for sub_expr in expr_ast[1:]:
                vars.update(find_old_vars(sub_expr))
    return vars

def z3_var(name):
    """Get a Z3 Int variable. Caches array declarations."""
    if name in ALL_VARS:
        # Check if it's used as an array (a bit of a hack)
        # In a real system, we'd have types.
        is_array = any(
            spec.get('modifies') and name in spec['modifies'] and 'a' in name.lower() 
            for spec in PROC_ENV.values()
        )
        if is_array:
             return Array(name, IntSort(), IntSort())
    return Int(name)

def z3_array(name):
    """Get a Z3 Array variable."""
    return Array(name, IntSort(), IntSort())


def expr_to_z3(expr, old_suffix=''):
    """Converts our AST expression to a Z3 expression."""
    if expr[0] == 'const':
        # Check for bool FIRST, since isinstance(True, int) is also True
        if isinstance(expr[1], bool):
            return BoolVal(expr[1])
        else:
            return IntVal(expr[1])
    
    elif expr[0] == 'var':
        # 'v' -> Int('v'). ALWAYS maps to the current state var.
        return Int(expr[1]) 
    
    elif expr[0] == 'old':
        # 'old(v)'
        # At verify_proc (suffix='_old'), map to v_old
        # At call_site (suffix=''), map to v_pre_call
        # (Your previous _pre_call logic was correct for this part)
        suffix_to_use = '_pre_call' if old_suffix == '' else old_suffix 
        return Int(f"{expr[1]}{suffix_to_use}")

    elif expr[0] == 'select':
        # Array read: a[i] or old(a)[i]
        arr_base_ast = expr[1]  # This is ['var', 'a'] or ['old', 'a']
        idx_ast = expr[2]
        idx_z3 = expr_to_z3(idx_ast, old_suffix) # Recursively call
        
        arr_name = arr_base_ast[1] # The name 'a'
        
        if arr_base_ast[0] == 'var':
            # a[i] -> Select(a, i). ALWAYS maps to current state array.
            arr_z3 = z3_array(arr_name)
            return Select(arr_z3, idx_z3)
        elif arr_base_ast[0] == 'old':
            # old(a)[i]
            # At verify_proc (suffix='_old'), map to a_old
            # At call_site (suffix=''), map to a_pre_call
            suffix_to_use = '_pre_call' if old_suffix == '' else old_suffix
            arr_z3 = z3_array(f"{arr_name}{suffix_to_use}")
            return Select(arr_z3, idx_z3)
        else:
            raise NotImplementedError(f"Unexpected array base in select: {arr_base_ast}")

    elif expr[0] in ('<', '<=', '>', '>=', '==', '!='):
        left = expr_to_z3(expr[1], old_suffix)
        right = expr_to_z3(expr[2], old_suffix)
        if expr[0] == '<': return left < right
        if expr[0] == '<=': return left <= right
        if expr[0] == '>': return left > right
        if expr[0] == '>=': return left >= right
        if expr[0] == '==': return left == right
        if expr[0] == '!=': return left != right
    
    elif expr[0] in ('+', '-', '*', '/'):
        left = expr_to_z3(expr[1], old_suffix)
        if len(expr) == 3:
            right = expr_to_z3(expr[2], old_suffix)
            if expr[0] == '+': return left + right
            if expr[0] == '-': return left - right
            if expr[0] == '*': return left * right
            if expr[0] == '/': return left / right
        else:
            # Unary minus
            return -left
    
    elif expr[0] in ('and', 'or', 'not'):
        if expr[0] == 'and':
            return And(expr_to_z3(expr[1], old_suffix), expr_to_z3(expr[2], old_suffix))
        if expr[0] == 'or':
            return Or(expr_to_z3(expr[1], old_suffix), expr_to_z3(expr[2], old_suffix))
        if expr[0] == 'not':
            return Not(expr_to_z3(expr[1], old_suffix))
            
    elif expr[0] == 'call_expr':
        func_id = expr[1]
        args_ast = expr[2]
        
        # Get or create the Z3 uninterpreted function
        if func_id not in Z3_FUNC_CACHE:
            # We need to know the 'arity' (number of args)
            # We get this from the procedure environment
            try:
                num_params = len(PROC_ENV[func_id]['params'])
            except KeyError:
                raise Exception(f"Using function '{func_id}' in expression, but it is not defined.")
            
            # Assume all args are Int, returns Int
            arg_types = [IntSort()] * num_params
            Z3_FUNC_CACHE[func_id] = Function(func_id, *arg_types, IntSort())
            
        z3_func = Z3_FUNC_CACHE[func_id]
        
        # Convert args to Z3, passing down the old_suffix
        z3_args = [expr_to_z3(a, old_suffix) for a in args_ast]
        
        return z3_func(*z3_args)
            
    else:
        raise NotImplementedError(f"expr_to_z3: {expr}")

def wp(stmt, post, ret_var=None, old_suffix=''):
    """Calculates the Weakest Precondition (WP)."""
    
    if stmt[0] == 'seq':
        for s in reversed(stmt[1:]):
            post = wp(s, post, ret_var, old_suffix)
        return post
    
    elif stmt[0] == 'assume':
        cond = expr_to_z3(stmt[1], old_suffix)
        return Implies(cond, post)
    
    elif stmt[0] == 'assert':
        cond = expr_to_z3(stmt[1], old_suffix)
        return And(cond, post)
    
    elif stmt[0] == 'if':
        test = expr_to_z3(stmt[1], old_suffix)
        body = stmt[2]
        orelse = stmt[3]
        wp_body = wp(body, post, ret_var, old_suffix)
        wp_orelse = wp(orelse, post, ret_var, old_suffix)
        return And(Implies(test, wp_body), Implies(Not(test), wp_orelse))
    
    elif stmt[0] == 'skip':
        return post
    
    elif stmt[0] == 'assign':
        # x = e
        var = stmt[1]
        expr = expr_to_z3(stmt[2], old_suffix)
        return substitute(post, (Int(var), expr))
        
    elif stmt[0] == 'tastore':
        # a[i] = e
        arr_name = stmt[1]
        arr = z3_array(arr_name)
        idx = expr_to_z3(stmt[2], old_suffix)
        val = expr_to_z3(stmt[3], old_suffix)
        new_arr = Store(arr, idx, val)
        return substitute(post, (arr, new_arr))
        
    elif stmt[0] == 'return':
        # return e
        assert ret_var is not None, "Return statement found outside function body"
        val = expr_to_z3(stmt[1], old_suffix)
        return substitute(post, (Int(ret_var), val))

    elif stmt[0] == 'invariant':
        # Invariants do not affect the WP calculation directly
        return post

    elif stmt[0] == 'while':
        cond = expr_to_z3(stmt[1], old_suffix)
        invariants = stmt[3]
        if not invariants:
             print(f"Warning: While loop has no invariants. Verification will likely fail.")
             # Fallback: treat as assert(False)
             return BoolVal(False)
             
        invariant = And(*[expr_to_z3(inv, old_suffix) for inv in invariants])
        body = ['seq'] + stmt[2]
        
        # 1. Invariant holds at loop entry
        vc_entry = invariant
        
        # 2. Invariant is preserved by loop body
        # WP(body, invariant)
        wp_body = wp(body, invariant, ret_var, old_suffix)
        vc_preservation = Implies(And(invariant, cond), wp_body)
        
        # 3. Invariant + exit condition implies postcondition
        vc_exit = Implies(And(invariant, Not(cond)), post)
        
        return And(vc_entry, vc_preservation, vc_exit)

    elif stmt[0] == 'proc':
        # Procedure definitions are handled separately, skip in WP
        return post
        
    elif stmt[0] == 'call':
        # x = f(e1, e2)
        fname, actuals, lhs = stmt[1], stmt[2], stmt[3]
        
        try:
            spec = PROC_ENV[fname]
        except KeyError:
            raise Exception(f"Attempted to call undefined procedure '{fname}'")
            
        params = spec['params']
        req = spec['requires']
        ens = spec['ensures']
        mod = spec['modifies']
        
        # --- 1. Precondition Check ---
        # Pre => requires[actuals/formals]
        req_z3 = expr_to_z3(req, old_suffix='') # old() maps to pre-call state
        subst_args_req = zip(map(Int, params), map(expr_to_z3, actuals))
        requires_subst = substitute(req_z3, list(subst_args_req))
        
        # --- 2. Havoc & Frame Condition ---
        # We must havoc *all* variables, then constrain them
        fresh_id = next_fresh_id()
        
        # Create fresh Z3 vars for the post-call state
        all_vars_fresh = {}
        for v in ALL_VARS:
            all_vars_fresh[v] = Int(f"{v}_{fresh_id}")
        
        # Z3 arrays for post-call state
        all_arrays_fresh = {}
        for v in ALL_VARS:
             # Simple heuristic: if it's in modifies, it *could* be an array
             if v in mod:
                all_arrays_fresh[v] = Array(f"{v}_{fresh_id}", IntSort(), IntSort())

        # Substitution list for Havoc: map Int('v') -> Int('v_fresh')
        subst_all_havoc = []
        for v in ALL_VARS:
            subst_all_havoc.append((Int(v), all_vars_fresh[v]))
            if v in all_arrays_fresh:
                subst_all_havoc.append((z3_array(v), all_arrays_fresh[v]))
                
        # Q[fresh/vars]
        Q_havoc = substitute(post, subst_all_havoc)
        
        # --- 3. Assume Postcondition & Frame ---
        # Build Ensures' = ensures_f[...] AND Frame
        
        # ensures_f[actuals/formals]
        # At a call site, old(v) in ensures maps to pre-call state 'v'
        # Post-state 'v' maps to 'v_fresh'
        ens_z3 = expr_to_z3(ens, old_suffix='') # old(v) -> Int(v)
        subst_args_ens = zip(map(Int, params), map(expr_to_z3, actuals))
        ens_subst_args = substitute(ens_z3, list(subst_args_ens))
        
        # ...[lhs/ret]
        if lhs:
            # ret maps to the *fresh* LHS var
            ens_subst_ret = substitute(ens_subst_args, (Int('ret'), all_vars_fresh[lhs]))
        else:
            ens_subst_ret = ens_subst_args
            
        # ...[fresh/vars] (for post-state vars in ensures)
        ens_havoc = substitute(ens_subst_ret, subst_all_havoc)
        
        # Frame Condition: ⋀v∉M (v_fresh = v_pre)
        mod_vars = set(mod)
        if lhs:
            mod_vars.add(lhs)
            
        frame_conds = []
        for v in ALL_VARS:
            if v not in mod_vars:
                # Add frame for scalar Ints
                frame_conds.append(all_vars_fresh[v] == Int(v))
                # Add frame for Arrays (Store-Select axiom)
                if v in all_arrays_fresh:
                     i = Int(f"i_frame_{fresh_id}")
                     frame_conds.append(
                         ForAll([i], Select(all_arrays_fresh[v], i) == Select(z3_array(v), i))
                     )

        Frame_Z3 = And(frame_conds)
        
        Ensures_Prime = And(ens_havoc, Frame_Z3)
        
        # --- 4. Final VC ---
        # Pre_Check AND (ForAll fresh_vars. (Ensures' => Q_havoc))
        
        # Gather all Z3 fresh vars to quantify over
        all_fresh_z3 = list(all_vars_fresh.values()) + list(all_arrays_fresh.values())
        
        vc_call = ForAll(all_fresh_z3, Implies(Ensures_Prime, Q_havoc))
        
        # Now, substitute the _pre_call vars with the actual pre-call state
        # (e.g., 'a_pre_call' -> 'a', 'x_pre_call' -> 'x')
        subst_pre_call = []
        for v in ALL_VARS:
            subst_pre_call.append( (Int(f"{v}_pre_call"), Int(v)) )
            subst_pre_call.append( (z3_array(f"{v}_pre_call"), z3_array(v)) )

        return And(requires_subst, substitute(vc_call, subst_pre_call))

    else:
        raise NotImplementedError(f"wp: {stmt}")

def verify_proc(name, spec):
    """Generates the VC for a single procedure."""
    print(f"  Verifying procedure {name}...")
    params = spec['params']
    body_ast = spec['body']
    req = spec['requires']
    ens = spec['ensures']
    
    # Find all old(v) in the 'ensures' clause
    old_vars = find_old_vars(ens)
    old_assumptions = []
    for v in old_vars:
        # Assume v_old == v at the start
        old_assumptions.append(Int(f"{v}_old") == Int(v))
        # Also handle arrays
        if 'a' in v: # Heuristic
             i = Int(f"i_old_frame_{v}")
             old_assumptions.append(
                 ForAll([i], Select(z3_array(f"{v}_old"), i) == Select(z3_array(v), i))
             )

    # Precondition: requires(...) AND (v_old == v)
    # Note: old_suffix='_old' maps old(v) -> v_old
    pre_z3 = expr_to_z3(req, old_suffix='_old')
    pre_with_olds = And(pre_z3, And(old_assumptions))
    
    # Postcondition: ensures(...)
    post_z3 = expr_to_z3(ens, old_suffix='_old')
    
    # VC: Pre => WP(body, Post)
    wp_body = wp(['seq'] + body_ast, post_z3, ret_var='ret', old_suffix='_old')
    
    vc = Implies(pre_with_olds, wp_body)
    
    # --- AXIOM PART ---
    # If the ensures clause uses this function recursively (as an uninterpreted function),
    # we must add the spec itself as an axiom.
    axiom = None
    if name in Z3_FUNC_CACHE:
        z3_func = Z3_FUNC_CACHE[name]
        
        # 1. Get Z3 vars for params
        param_z3_vars = [Int(p) for p in params]
        
        # 2. Get Z3 vars for old_vars
        old_z3_vars = []
        for v in old_vars:
            old_z3_vars.append(Int(f"{v}_old"))
            if 'a' in v: # Simple heuristic
                old_z3_vars.append(z3_array(f"{v}_old"))

        all_axiom_vars = param_z3_vars + old_z3_vars

        # 3. Build axiom body
        # We must use the same '_old' suffix as verify_proc
        ens_axiom_body = expr_to_z3(ens, old_suffix='_old')
        req_axiom_body = expr_to_z3(req, old_suffix='_old')
        
        # 4. Substitute 'ret' with 'func_call'
        axiom_body = substitute(ens_axiom_body, (Int('ret'), z3_func(*param_z3_vars)))
        
        # 5. Create axiom: ForAll(vars, Requires => Ensures)
        # This defines the uninterpreted function
        axiom = ForAll(all_axiom_vars, Implies(req_axiom_body, axiom_body))

    # Check this specific VC
    s_proc = Solver()

    # --- ADD AXIOM TO SOLVER ---
    if axiom is not None:
        print(f"  ...Adding axiom for {name}")
        s_proc.add(axiom)
            
    s_proc.add(Not(vc))
    
    # Check the VC
    result = s_proc.check()

    if result == unsat:
        print(f"  ...Procedure {name} VERIFIED.")
        return True
    elif result == sat:
        print(f"  ...Procedure {name} FAILED verification.")
        print("  Counterexample:")
        print(f"  {s_proc.model()}")
        return False
    else: # result == unknown
        print(f"  ...Procedure {name} FAILED verification (Solver returned UNKNOWN).")
        print("  This is common with complex quantifier/array axioms.")
        try:
            print(f"  Solver reason: {s_proc.reason_unknown()}")
        except Z3Exception:
            pass # reason_unknown() can also fail
        return False

def prove(filename):
    """Main proving function."""
    global PROC_ENV, ALL_VARS
    
    # 1. Parse the file
    tree = py_ast(filename)
    visitor = WhilePyVisitor()
    parsed = visitor.visit(tree)
    
    main_stmt = parsed['main']
    PROC_ENV = parsed['procs']
    ALL_VARS = parsed['vars']
    
    # Add 'ret' to all vars if any procedures exist
    if PROC_ENV:
        ALL_VARS.add('ret')
        
    print("--- Program AST ---")
    pprint.pprint(main_stmt)
    print("\n--- Procedures ---")
    pprint.pprint(PROC_ENV)
    print("\n--- Variables ---")
    pprint.pprint(ALL_VARS)
    print("-" * 20)
    
    # 2. Verify all procedures
    all_procs_verified = True
    if PROC_ENV:
        print("--- Verifying Procedures ---")
        for name, spec in PROC_ENV.items():
            if not verify_proc(name, spec):
                all_procs_verified = False
        if not all_procs_verified:
            print("Verification failed for one or more procedures. Halting.")
            return
        print("--- All procedures verified ---")
    
    # 3. Verify main program
    print("\n--- Verifying Main Program ---")
    post = BoolVal(True)
    pre = wp(main_stmt, post)
    
    print("\nFinal VC (simplified):")
    print(simplify(pre))
    
    s = Solver()
    s.add(Not(pre))
    
    if s.check() == unsat:
        print("\nProgram is VERIFIED.")
    else:
        print("\nProgram is INCORRECT.")
        print("Counterexample:")
        print(s.model())

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python prover.py <filename.py>")
        sys.exit(1)
        
    filename = sys.argv[1]
    prove(filename)