# To add a new cell, type ''
# To add a new markdown cell, type ' [markdown]'

from copy import copy, deepcopy
from enum import Enum

class LitState(Enum):
    L_UNSAT = -1
    L_SAT = 1
    L_UNASSIGNED = 0

class ClauseState(Enum):
    C_UNSAT = 1
    C_SAT = 2
    C_UNIT = 3
    C_UNDEF = 4

class SolverState(Enum):
    UNSAT = 1
    SAT = 2
    CONFLICT = 3
    UNDEF = 4


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

    def next_not_false(self, is_left_watch, other_watch):
        assert(len(self.literals) >= 2)
        if (len(self.literals) > 2):
            for i, lit in enumerate(self.literals):
                lit_state = my_solver.lit_state(lit)
                if (lit_state != LitState.L_UNSAT and lit != other_watch):
                    if (is_left_watch):
                        self.left_watch = i
                    else:
                        self.right_watch = i
                    return i, ClauseState.C_UNDEF
        
        other_lit_state = my_solver.lit_state(other_watch)
        if (other_lit_state == LitState.L_UNSAT):
            return -1, ClauseState.C_UNSAT
        elif (other_lit_state == LitState.L_UNASSIGNED):
            return -1, ClauseState.C_UNIT
        else:
            return -1, ClauseState.C_SAT
            



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

    def lit_state(self, lit):
        var_state = self.state[Helper.litToVar(lit)]
        if (var_state == 0):
            return LitState.L_UNASSIGNED
        elif (var_state == -1 and (lit & 1)):
            return LitState.L_SAT
        elif (var_state == 1 and not (lit & 1)):
            return LitState.L_SAT
        else:
            return LitState.L_UNSAT

    def assert_lit(self, lit):
        self.trail.append(lit)
        var = Helper.litToVar(lit)
        if (lit & 1):
            self.state[var] = -1
            self.prev_state[var] = -1
        else:
            self.state[var] = 1
            self.prev_state[var] = 1

        self.dlevel[var] = self.dl
        self.num_assignments += 1
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
                if self.lit_state(lit) == LitState.L_SAT:
                    clause_satisfied = True
            if not clause_satisfied:
                print("Assignment faild at clause " + str(i+1))
        return

    def print_states(self):
        print(self.state)

    def BCP(self):
        while (len(self.BCP_stack) > 0):
            lit = self.BCP_stack[-1]
            assert(self.lit_state(lit) == LitState.L_UNSAT)
            self.BCP_stack.pop()
            new_watch_list = [0 for i in self.watches[lit]]
            new_watch_list_idx = len(self.watches[lit]) - 1
            for i, clause_idx in enumerate(self.watches[lit][::-1]):
                if (self.conflicting_clause_idx >= 0):
                    break
                clause = self.cnf[clause_idx]
                l_watch = clause.left_watch
                r_watch = clause.right_watch
                is_left_watch = l_watch == lit
                other_watch =  r_watch if is_left_watch else l_watch
                new_watch_loc, res = clause.next_not_false(is_left_watch, other_watch)
                if (res != ClauseState.C_UNDEF):
                    new_watch_list[new_watch_list_idx] = clause_idx
                    new_watch_list_idx -= 1
                
                if (res == ClauseState.C_UNSAT):
                    if (self.dl == 0):
                        return SolverState.UNSAT
                    self.conflicting_clause_idx = clause_idx
                    self.BCP_stack.clear()
                    start_i = len(self.watches[lit])-i-1
                    for other_clause_idx in self.watches[lit][start_i::-1]:
                        new_watch_list[new_watch_list_idx] = other_clause_idx

                elif (res == ClauseState.C_UNIT):
                    self.assert_lit(other_watch)
                    self.BCP_stack.append(Helper.opposite(other_watch))
                    self.antecedent[Helper.litToVar(other_watch)] = clause_idx

                elif (res == ClauseState.C_UNDEF):
                    assert(new_watch_loc >= 0 and new_watch_loc < len(clause.literals))
                    new_lit = clause.literals[new_watch_loc]
                    self.watches[new_lit].append(clause_idx)
            
            self.watches[lit].clear()
            new_watch_list_idx += 1
            self.watches[lit] = list(new_watch_list[new_watch_list_idx:])
            if (self.conflicting_clause_idx >= 0):
                return SolverState.CONFLICT
            else:
                new_watch_list.clear()

        return SolverState.UNDEF


if True:
    my_solver = Solver()
    filename = "E:/Studies/SEM8/OM/Assignment/test/unsat/my_test.cnf"
    my_solver.read_input(filename)
    # for clause in my_solver.cnf:
    #     print(clause.literals)
    my_solver.print_states()
    my_solver.validate_assignment()





