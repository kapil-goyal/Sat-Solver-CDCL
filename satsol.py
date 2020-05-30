from copy import copy, deepcopy
from enum import Enum
import cProfile 
import random
import time

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

    @staticmethod
    def litToRLit(lit):
        if (lit & 1):
            return -Helper.litToVar(lit)
        else:
            return Helper.litToVar(lit)



class Clause:
    def __init__(self):
        self.literals = list()
        self.left_watch = int()
        self.right_watch = int()
        self.prev_clause = int()
        self.next_clause = int()

    def insert_lit(self, solver, inp_lit, max_var):
        assert(int(inp_lit) <= int(max_var))
        solver.bumpVarScore(abs(int(inp_lit)))
        self.literals.append(Helper.varToLit(int(inp_lit)))

    def insert(self, solver, new_clause, max_var):
        new_clause = list(set(new_clause))
        for lit in new_clause:
            if lit is not "0":
                self.insert_lit(solver, lit, max_var)

    def next_not_false(self, solver, is_left_watch, other_watch):
        assert(len(self.literals) >= 2)
        if (len(self.literals) > 2):
            for i, lit in enumerate(self.literals):
                lit_state = solver.lit_state(lit)
                if (lit_state != LitState.L_UNSAT and lit != other_watch):
                    if (is_left_watch):
                        self.left_watch = i
                    else:
                        self.right_watch = i
                    return i, ClauseState.C_UNDEF
        
        other_lit_state = solver.lit_state(other_watch)
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
        self.m_var_inc = 1.0
        self.m_curr_activity = 1.0
        self.num_learned = 0
        self.num_decisions = 0

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
                self.initialize()
            else:
                assert(p_encountered)

                new_clause = Clause()
                new_clause.insert(self, line, self.num_vars)
                assert(len(new_clause.literals) != 0)
                self.cnf.append(new_clause)
                del new_clause
                
                clauses_count += 1

        # assert(self.num_clause == clauses_count)
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

    def bumpVarScore(self, var_idx):
        self.m_activity[var_idx] += self.m_var_inc
        return

    def add_unary_clause(self, lit):
        self.unaries.append(lit)
        return

    def getVal(self, var):
        saved_phase = self.prev_state[var]
        if (saved_phase == -1 or saved_phase == 0):
            return Helper.varToLit(-var)
        elif (saved_phase == 1):
            return Helper.varToLit(var)
        else:
            assert(False)

    def heuristic(self):
        self.count_arr = [0 for i in range(self.num_vars+1)]
        for clause in self.cnf:
            for lit in clause.literals:
                self.count_arr[Helper.litToVar(lit)] += 1
        
        self.one_time_vars = set()
        for idx, count in enumerate(self.count_arr):
            if count == 1:
                self.one_time_vars.add(idx)

    def heuristic2(self):
        for idx, clause in enumerate(self.cnf):
            found = False
            for lit in clause.literals:
                var = Helper.litToVar(lit)
                if (var in self.one_time_vars):
                    found = True
                    self.one_time_vars.remove(var)
                    break
            if (found):
                for lit in clause.literals:
                    var = Helper.litToVar(lit)
                    self.count_arr[var] -= 1
                    if (self.count_arr[var] == 1):
                        self.one_time_vars.add(var)
                del self.cnf[idx]

    def heuristic3(self):
        while (True):
            self.heuristic()
            if (len(self.one_time_vars) == 0):
                break
            self.heuristic2()

    def process_input(self):
        self.heuristic3()
        random.shuffle(self.cnf)
        new_cnf = list()
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
                self.watches[clause.literals[0]].append(len(new_cnf))
                self.watches[clause.literals[1]].append(len(new_cnf))
                new_cnf.append(clause)

        del self.cnf
        self.cnf = new_cnf

    def get_best_var(self):
        best_var = 0
        max_score = 0
        for var, score in enumerate(self.m_activity):
            if (self.state[var] == 0 and max_score < score):
                max_score = score
                best_var = var

        return best_var

    def decide(self):
        best_var = self.get_best_var()        
        best_lit = self.getVal(best_var)

        if (best_var == 0 or best_lit == 0):
            return SolverState.SAT

        # Apply decision
        self.dl += 1
        if (self.dl > self.max_dl):
            self.max_dl = self.dl
            self.separators.append(len(self.trail))
            self.conflicts_at_dl.append(self.num_learned)
        else:
            self.separators[self.dl] = (len(self.trail))
            self.conflicts_at_dl[self.dl] = self.num_learned

        self.assert_lit(best_lit)
        self.num_decisions += 1
        self.BCP_stack.append(Helper.opposite(best_lit))
        return SolverState.UNDEF

    def analyze(self, conflicting_clause):
        current_clause = (conflicting_clause)
        new_clause = Clause()
        resolve_num = 0
        bktrk = 0
        watch_lit = 0
        antecedents_idx = 0
        removed = set()

        u = int()
        v = int()
        while (True):
            for lit in current_clause.literals:
                if lit not in removed:
                    v = Helper.litToVar(lit)
                    if (self.marked[v] == False):
                        self.marked[v] = True
                        if (self.dlevel[v] == self.dl):
                            resolve_num += 1
                        else:
                            new_clause.literals.append(lit)
                            c_dl = self.dlevel[v]
                            if (c_dl > bktrk):
                                bktrk = c_dl
                                watch_lit = len(new_clause.literals) - 1

            for lit in self.trail[::-1]:
                v = Helper.litToVar(lit)
                u = lit
                if (self.marked[v] == True):
                    break

            self.marked[v] = False
            resolve_num -= 1
            if (resolve_num == 0):
                break

            ant = self.antecedent[v]
            current_clause = (self.cnf[ant])
            removed.add(u)
            # current_clause.literals.remove(u)

            if (resolve_num <= 0):
                break
        
        for lit in new_clause.literals:
            self.marked[Helper.litToVar(lit)] = False
        
        opp_u = Helper.opposite(u)
        new_clause.literals.append(opp_u)
        self.m_var_inc *= 1 / 0.95
        self.num_learned += 1
        self.asserted_lit = opp_u

        if (len(new_clause.literals) == 0):
            self.BCP_stack.append(u)
            self.add_unary_clause(opp_u)
        else:
            self.BCP_stack.append(u)
            new_clause.right_watch = len(new_clause.literals)-1
            new_clause.left_watch = watch_lit
            self.watches[new_clause.literals[new_clause.left_watch]].append(len(self.cnf))
            self.watches[new_clause.literals[new_clause.right_watch]].append(len(self.cnf))
            self.cnf.append(new_clause)
                
        return bktrk

    def backtrack(self, k):
        for lit in self.trail[self.separators[k+1]:]:
            v = Helper.litToVar(lit)
            if (self.dlevel[v] > 0):
                self.state[v] = 0

        self.trail = self.trail[:self.separators[k+1]]
        self.dl = k
        if (k == 0):
            self.assert_unary(self.asserted_lit)
        else:
            self.assert_lit(self.asserted_lit)
        self.antecedent[Helper.litToVar(self.asserted_lit)] = len(self.cnf)-1
        self.conflicting_clause_idx = -1

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
                l_watch = clause.literals[clause.left_watch]
                r_watch = clause.literals[clause.right_watch]
                is_left_watch = l_watch == lit
                other_watch =  r_watch if is_left_watch else l_watch
                new_watch_loc, res = clause.next_not_false(self, is_left_watch, other_watch)
                if (res != ClauseState.C_UNDEF):
                    new_watch_list[new_watch_list_idx] = clause_idx
                    new_watch_list_idx -= 1
                
                if (res == ClauseState.C_UNSAT):
                    if (self.dl == 0):
                        return SolverState.UNSAT
                    self.conflicting_clause_idx = clause_idx
                    self.BCP_stack.clear()
                    start_i = len(self.watches[lit])-i-1
                    if (start_i > 0):
                        for other_clause_idx in self.watches[lit][start_i-1::-1]:
                            new_watch_list[new_watch_list_idx] = other_clause_idx
                            new_watch_list_idx -= 1

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

    def _solve(self):
        # res = SolverState()
        while (True):
            while (True):
                res = self.BCP()
                if (res == SolverState.UNSAT):
                    return res
                if (res == SolverState.CONFLICT):
                    self.backtrack(self.analyze(self.cnf[self.conflicting_clause_idx]))
                else:
                    break

            res = self.decide()
            if (res == SolverState.SAT or res == SolverState.UNSAT):
                return res

    def solve(self):
        res = self._solve()
        assert(res == SolverState.SAT or res == SolverState.UNSAT)
        return res
        # print(res)

def print_stats(solver, filename, res, duration):
    ans = "Satifiable" if res == SolverState.SAT else "Unsatisfiable"
    print("")
    print("Statistics")
    print("========================================================")
    print(filename)
    print("========================================================")
    print(ans)
    print("========================================================")
    print("Learned Clauses:\t" + str(solver.num_learned))
    print("Decisios:\t\t" + str(solver.num_decisions))
    print("Implications:\t\t" + str(solver.num_assignments - solver.num_decisions))
    minutes, seconds = divmod(duration, 60)
    print("Time:\t\t\t" + str(minutes) + " minutes " + str(seconds) + " seconds")


def read_file_and_solve_sat(filename):
    global my_solver
    start_time = time.time()
    my_solver.read_input(filename)
    res = my_solver.solve()
    if (res == SolverState.SAT):
        my_solver.validate_assignment()
    end_time = time.time()
    print_stats(my_solver, filename, res, end_time - start_time)

my_solver = Solver()
filename = "E:/Studies/SEM8/OM/Assignment/test/sat/bmc-2.cnf"
read_file_and_solve_sat(filename)




