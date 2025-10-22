import ast
import pprint

def py_ast(filename):
    with open(filename, "r") as f:
        tree = ast.parse(f.read(), filename=filename)
        return tree

class WhilePyVisitor(ast.NodeVisitor):
    def visit_Module(self, node):
        nodes = list(map(self.visit, node.body))
        return ['seq'] + nodes
    
    def visit_Expr(self, node):
        return self.visit(node.value)
    
    def visit_Call(self, node):
        if isinstance(node.func, ast.Name):
            if node.func.id == 'assume':
                assert len(node.args) == 1
                return ['assume', self.visit(node.args[0])]
            elif node.func.id == 'assert':
                assert len(node.args) == 1
                return ['assert', self.visit(node.args[0])]
            elif node.func.id == 'invariant':
                assert len(node.args) == 1
                return ['invariant', self.visit(node.args[0])]
        raise NotImplementedError(ast.dump(node))
    
    def visit_Const(self, node):
        assert isinstance(node.value, (int, bool))
        return ['const', node.value]
    
    def visit_Constant(self, node):
        assert isinstance(node.value, (int, bool))
        return ['const', node.value]
    
    def visit_If(self, node):
        test = self.visit(node.test)
        body = list(map(self.visit, node.body))
        orelse = list(map(self.visit, node.orelse))
        if len(orelse) == 0:
            orelse = [['skip']]
        return ['if', test, body, orelse]
    
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
        return ['var', node.id]
    
    def visit_UnaryOp(self, node):
        assert isinstance(node.op, ast.USub)
        operand = self.visit(node.operand)
        return ['-', operand]
    
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
            return ['/', left, right]
        else:
            raise NotImplementedError(ast.dump(node))
    
    def visit_Assign(self, node):
        assert len(node.targets) == 1
        target = node.targets[0]
        assert isinstance(target, ast.Name)
        var = target.id
        value = self.visit(node.value)
        return ['assign', var, value]
    
    def visit_Pass(self, node):
        return ['skip']
    
    def visit_Assert(self, node):
        test = self.visit(node.test)
        return ['assert', test]
    
    def visit_While(self, node):
        test = self.visit(node.test)
        body = list(map(self.visit, node.body))
        invariants = []
        for stmt in node.body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                call = stmt.value
                if isinstance(call.func, ast.Name) and call.func.id == 'invariant':
                    assert len(call.args) == 1
                    inv = self.visit(call.args[0])
                    invariants.append(inv)
        return ['while', test, body, invariants]
    
    def generic_visit(self, node):
        raise NotImplementedError(ast.dump(node))

# tree = py_ast("parse_example.py")
# visitor = WhilePyVisitor()
# stmt = visitor.visit(tree)
# pprint.pprint(stmt)
