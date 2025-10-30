import ast
import pprint
import sys

class WhilePyVisitor(ast.NodeVisitor):
    def __init__(self):
        self.vars = set()
        self.procs = {}

    def visit_Module(self, node):
        # First pass to register all procedure definitions
        for stmt in node.body:
            if isinstance(stmt, ast.FunctionDef):
                self.visit_FunctionDef(stmt)
        
        # Second pass to build the main program body
        main_body = []
        for stmt in node.body:
            if not isinstance(stmt, ast.FunctionDef):
                main_body.append(self.visit(stmt))
                
        return {'main': ['seq'] + main_body, 'procs': self.procs, 'vars': self.vars}
    
    def visit_BoolOp(self, node):
        assert isinstance(node.op, (ast.And, ast.Or))
        op_str = 'and' if isinstance(node.op, ast.And) else 'or'
        
        # Build a right-associative tree, e.g., a and b and c -> ['and', a, ['and', b, c]]
        visited_values = [self.visit(v) for v in node.values]
        
        current = visited_values[-1]
        for val in reversed(visited_values[:-1]):
            current = [op_str, val, current]
        return current

    def visit_Expr(self, node):
        # Handle standalone calls like 'proc_without_return(x)'
        if isinstance(node.value, ast.Call):
            call = node.value
            if isinstance(call.func, ast.Name):
                func_id = call.func.id
                if func_id not in ('assume', 'assert', 'invariant', 'requires', 'ensures', 'modifies'):
                    args = [self.visit(a) for a in call.args]
                    return ['call', func_id, args, None] # No LHS
        return self.visit(node.value)
    
    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            func_id = node.func.id
            if func_id == 'assume':
                assert len(node.args) == 1
                return ['assume', self.visit(node.args[0])]
            elif func_id == 'assert':
                assert len(node.args) == 1
                return ['assert', self.visit(node.args[0])]
            elif func_id == 'invariant':
                assert len(node.args) == 1
                return ['invariant', self.visit(node.args[0])]
            elif func_id == 'old':
                 assert len(node.args) == 1
                 # We extract the variable name, e.g., ['var', 'x'] -> 'x'
                 return ['old', self.visit(node.args[0])[1]]
            
            # This is a regular function call used as an expression
            # e.g., sum_array(n-1) inside an 'ensures' clause
            else:
                args = [self.visit(a) for a in node.args]
                # We create a new AST node type: 'call_expr'
                return ['call_expr', func_id, args]
        
        raise NotImplementedError(f"Unexpected call expression: {ast.dump(node)}")    
    def visit_Const(self, node):
        assert isinstance(node.value, (int, bool))
        return ['const', node.value]
    
    def visit_Constant(self, node):
        # For Python 3.8+
        assert isinstance(node.value, (int, bool))
        return ['const', node.value]
    
    def visit_If(self, node):
        test = self.visit(node.test)
        body = list(map(self.visit, node.body))
        orelse = list(map(self.visit, node.orelse))
        if len(orelse) == 0:
            orelse = [['skip']]
        return ['if', test, ['seq'] + body, ['seq'] + orelse]
    
    def visit_Compare(self, node):
        assert len(node.ops) == 1
        assert len(node.comparators) == 1
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        op = node.ops[0]
        if isinstance(op, ast.Lt):
            return ['<', left, right]
        elif isinstance(op, ast.LtE):
            return ['<=', left, right]
        elif isinstance(op, ast.Gt):
            return ['>', left, right]
        elif isinstance(op, ast.GtE):
            return ['>=', left, right]
        elif isinstance(op, ast.Eq):
            return ['==', left, right]
        elif isinstance(op, ast.NotEq):
            return ['!=', left, right]
        else:
            raise NotImplementedError(ast.dump(node))
    
    def visit_Name(self, node):
        self.vars.add(node.id)
        return ['var', node.id]
    
    def visit_UnaryOp(self, node):
            # assert isinstance(node.op, ast.USub) # <--- Remove this line
            if isinstance(node.op, ast.USub):
                operand = self.visit(node.operand)
                return ['-', operand]
            elif isinstance(node.op, ast.Not):
                operand = self.visit(node.operand)
                return ['not', operand]
            
            raise NotImplementedError(ast.dump(node))
    
    def visit_BinOp(self, node):
        left = self.visit(node.left)
        right = self.visit(node.right)
        if isinstance(node.op, ast.Add):
            return ['+', left, right]
        elif isinstance(node.op, ast.Sub):
            return ['-', left, right]
        elif isinstance(node.op, ast.Mult):
            return ['*', left, right]
        elif isinstance(node.op, ast.Div):
            # Note: This is integer division in Z3
            return ['/', left, right]
        else:
            raise NotImplementedError(ast.dump(node))

    def visit_Assign(self, node):
        assert len(node.targets) == 1
        target = node.targets[0]
        
        if isinstance(target, ast.Name):
            var = target.id
            self.vars.add(var)
            
            # Handle procedure call: x = f(y)
            if isinstance(node.value, ast.Call):
                call = node.value
                if isinstance(call.func, ast.Name):
                    func_id = call.func.id
                    if func_id not in ('assume', 'assert', 'invariant', 'old'):
                        args = [self.visit(a) for a in call.args]
                        return ['call', func_id, args, var] # LHS is 'var'
            
            # Handle standard assignment: x = e
            # NOW it's safe to visit the value
            value = self.visit(node.value) 
            return ['assign', var, value]
            
        elif isinstance(target, ast.Subscript):
            # Handle array write: a[i] = e
            arr_name_ast = self.visit(target.value)
            assert arr_name_ast[0] == 'var', "Array base must be a variable"
            arr_name = arr_name_ast[1]
            self.vars.add(arr_name)
            
            index = self.visit(target.slice)
            value = self.visit(node.value) 
            return ['tastore', arr_name, index, value]
            
        raise NotImplementedError(ast.dump(node))
        
    def visit_Subscript(self, node):
            # Handle array read: a[i] or old(a)[i]
            assert isinstance(node.ctx, ast.Load), "Subscript on LHS handled by visit_Assign"
            arr_base_ast = self.visit(node.value) # e.g., ['var', 'a'] or ['old', 'a']
            index_ast = self.visit(node.slice)
            
            # The base must be 'var' or 'old'
            assert arr_base_ast[0] in ('var', 'old'), f"Array base must be a variable or old(var), not {arr_base_ast[0]}"
            
            # Return ['select', BASE_AST, INDEX_AST]
            return ['select', arr_base_ast, index_ast]

    def visit_Index(self, node):
        # Helper for Subscript in Python < 3.9
        return self.visit(node.value)

    def visit_Pass(self, node):
        return ['skip']
    
    def visit_Assert(self, node):
        test = self.visit(node.test)
        return ['assert', test]
    
    def visit_Return(self, node):
        return ['return', self.visit(node.value)]

    def visit_FunctionDef(self, node):
        name = node.name
        params = [a.arg for a in node.args.args]
        self.vars.update(params)
        
        requires = ['const', True]
        ensures = ['const', True]
        modifies = []
        body_stmts = []

        # Parse contracts from docstring or body
        for stmt in node.body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call) and isinstance(stmt.value.func, ast.Name):
                call = stmt.value
                func_id = call.func.id
                
                if func_id == 'requires':
                    assert len(call.args) == 1
                    requires = self.visit(call.args[0])
                elif func_id == 'ensures':
                    assert len(call.args) == 1
                    ensures = self.visit(call.args[0])
                elif func_id == 'modifies':
                    # Expects modifies("x", "y", ...)
                    mod_vars = []
                    for arg in call.args:
                        if isinstance(arg, ast.Constant): # Python 3.8+
                            mod_vars.append(arg.value)
                        elif isinstance(arg, ast.Str): # Python < 3.8
                            mod_vars.append(arg.s)
                    modifies = mod_vars
                    self.vars.update(modifies)
                else:
                    body_stmts.append(stmt)
            else:
                body_stmts.append(stmt)
                
        body = [self.visit(s) for s in body_stmts]
        
        proc_info = {
            'params': params, 
            'body': body, 
            'requires': requires, 
            'ensures': ensures, 
            'modifies': modifies
        }
        self.procs[name] = proc_info
        # We return a 'proc' node, but it's mainly for completeness.
        # The main 'prove' function will use self.procs
        return ['proc', name, params, body, requires, ensures, modifies]

    def visit_While(self, node):
        test = self.visit(node.test)
        
        body_stmts = []
        invariants = []
        for stmt in node.body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call = stmt.value
                if isinstance(call.func, ast.Name) and call.func.id == 'invariant':
                    assert len(call.args) == 1
                    inv = self.visit(call.args[0])
                    invariants.append(inv)
                else:
                    body_stmts.append(stmt)
            else:
                body_stmts.append(stmt)
                
        body = [self.visit(s) for s in body_stmts]
        return ['while', test, body, invariants]
    
    def generic_visit(self, node):
        raise NotImplementedError(f"Unsupported AST node: {ast.dump(node)}")

def py_ast(filename):
    with open(filename, "r") as f:
        tree = ast.parse(f.read(), filename=filename)
        return tree


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python parser.py <filename.py>")
        sys.exit(1)
        
    filename = sys.argv[1]
    tree = py_ast(filename)
    visitor = WhilePyVisitor()
    parsed_program = visitor.visit(tree)
    
    print("--- Parsed Main Program ---")
    pprint.pprint(parsed_program['main'])
    print("\n--- Detected Procedures ---")
    pprint.pprint(parsed_program['procs'])
    print("\n--- Detected Variables ---")
    pprint.pprint(parsed_program['vars'])