# To add a new cell, type ''
# To add a new markdown cell, type ' [markdown]'

from copy import copy, deepcopy



class Helper:

    @staticmethod
    def varToLit(v):
        if (v < 0):
            return (2 * -v) - 1
        else:
            return 2 * v

    @staticmethod
    def opposite(lit):
        if (lit & 1):
            return lit + 1
        else:
            return lit - 1

    @staticmethod
    def litToVar(lit):
        return int((lit + 1) / 2)



class Clause:
    def __init__(self):
        self.literals = list()
        self.left_watch = int()
        self.right_watch = int()
        self.prev_clause = int()
        self.next_clause = int()

    def insert_lit(self, inp_lit, max_var):
        assert(int(inp_lit) <= int(max_var))
        self.literals.append(Helper.varToLit(int(inp_lit)))

    def insert(self, new_clause, max_var):
        for lit in new_clause:
            if lit is not "0":
                self.insert_lit(lit, max_var)



class Solver:
    
    def __init__(self):
        self.cnf = list()

        self.num_vars = int()
        self.num_clause = int()
        self.num_lits = int()

        self.num_assignments = 0
        self.conflicting_clause_idx = -1
        self.dl = 0
        self.max_dl = 0

        self.unaries = list()
        self.trail = list()
        self.BCP_stack = list()
        self.state = list()
        self.prev_state = list()
        self.watches = list()
        self.separators = list()
        self.antecedent = list()
        self.marked = list()
        self.dlevel = list()
        self.conflicts_at_dl = list()
        self.m_activity = list()

    def read_input(self, filename):
        f = open(filename)
        lines = [line.split() for line in f]
        p_encountered = False
        clauses_count = 0
        assert(len([1 for line in lines if line[0] == 'p']) == 1)
        for line in lines:
            if line[0] == 'c':
                continue
            elif line[0] == 'p':
                p_encountered = True
                self.num_vars = int(line[2])
                self.num_clause = int(line[3])
            else:
                assert(p_encountered)

                new_clause = Clause()
                new_clause.insert(line, self.num_vars)
                assert(len(new_clause.literals) != 0)
                my_solver.cnf.append(new_clause)
                del new_clause
                
                clauses_count += 1

        assert(self.num_clause == clauses_count)
        self.initialize()
        self.process_input()
        return

    def initialize(self):
        self.num_lits = 2 * self.num_vars
        self.state = [0 for _ in range(0, self.num_vars + 1)]
        self.prev_state = [0 for _ in range(0, self.num_vars + 1)]
        self.antecedent = [-1 for _ in range(0, self.num_vars + 1)]
        self.marked = [False for _ in range(0, self.num_vars + 1)]
        self.dlevel = [0 for _ in range(0, self.num_vars + 1)]
        self.m_activity = [0 for _ in range(0, self.num_vars + 1)]
        self.watches = [[] for _ in range(0, self.num_lits + 1)]

        self.dl = 0
        self.conflicting_clause_idx = -1
        self.separators.append(0)
        self.conflicts_at_dl.append(0)
        return

    def assert_unary(self, lit):
        var = Helper.litToVar(lit)
        if (lit & 1):
            self.state[var] = -1
        else:
            self.state[var] = 1

        self.dlevel[var] = self.dl
        self.num_assignments += 1
        return 

    def add_unary_clause(self, lit):
        self.unaries.append(lit)
        return


    def process_input(self):
        for i, clause in enumerate(self.cnf):
            assert(len(clause.literals) > 0)
            if (len(clause.literals) == 1):
                lit = clause.literals[0]
                self.assert_unary(lit)
                self.BCP_stack.append(Helper.opposite(lit))
                self.add_unary_clause(lit)
            else:
                clause.left_watch = 0
                clause.right_watch = 1
                self.watches[0].append(i)
                self.watches[1].append(i)

    def validate_assignment(self):
        for i, clause in enumerate(self.cnf):
            clause_satisfied = False
            for lit in clause.literals:
                var_state = self.state[Helper.litToVar(lit)]
                if (var_state < 0 and lit & 1) or (var_state > 0 and not (lit & 1)):
                    clause_satisfied = True
            if not clause_satisfied:
                print("Assignment faild at clause " + str(i+1))
        return

    def print_states(self):
        print(self.state)


if True:
    my_solver = Solver()
    filename = "E:/Studies/SEM8/OM/Assignment/test/unsat/my_test.cnf"
    my_solver.read_input(filename)
    for clause in my_solver.cnf:
        print(clause.literals)
    my_solver.print_states()
    my_solver.validate_assignment()





