import sys
import importlib
import types
import functools
import copy
from itertools import combinations

solution = {}
variables = []
attributes = []
values = {}
constraints = []
affirmations = []
question = []
arcs = []
dom_per_var = {}
dom_per_var_p = {}
key_words = ["first", "middle", "last", "right", "left", "next"]
first = 1
middle = 3
last = 5

def read_input():
    f = open(sys.argv[1])
    global data
    loader = importlib.machinery.SourceFileLoader('data', sys.argv[1])
    data = types.ModuleType(loader.name)
    loader.exec_module(data)
    global attributes, values, affirmations, question
    attributes = [x.lower() for x in data.A]
    values = dict((k.lower(), [x.lower() for x in v]) for k,v in data.D.items())
    affirmations = [x.lower() for x in data.Text.split(".")]
    question = data.Q.lower()
    f.close()

def make_all_variables():
    global attributes
    global dom_per_var_p
    for category in values.keys():
        for elem in values[category]:
            variables.append(elem)
            dom_per_var[elem] = list(range(5))
    dom_per_var_p = copy.deepcopy(dom_per_var)

def value_constraint(v, x0):
    return v == x0

def diff_value_constraint(v, x0):
    return v != x0

def different_values(x0, x1):
    return x0 != x1

def two_values_constraint(x0, x1):
    return x0 == x1

def right_constraint(x0,x1):
    return (x0 - x1) == 1

def next_constraint(x0,x1):
    return abs(x0-x1) == 1

def make_2_value_constr(afr):
    val1 = ""
    val2 = ""
    done = False

    for x in values:
        for val in values[x]:
            if val in afr:
                if val1 == "" :
                    val1 = val
                else:
                    val2 = val
                    done = True
        if done:
            break

    if afr.index(val1) > afr.index(val2):
        aux = val1
        val1 = val2
        val2 = aux

    return [[val1, val2], two_values_constraint]

def make_first_const(afr):
    val1 = ""

    done = False
    for x in values:
        for val in values[x]:
            if val in afr:
                val1 = val
                done = True
        if done:
            break

    dom_per_var[val1] = [0]
    dom_per_var_p[val1] = [0]

    return []

def make_middle_const(afr):
    val1 = ""

    done = False
    for x in values:
        for val in values[x]:
            if val in afr:
                type1 = x
                val1 = val
                done = True
        if done:
            break

    dom_per_var[val1] = [2]
    dom_per_var_p[val1] = [2]

    return []

def make_last_const(afr):
    val1 = ""

    done = False
    for x in values:
        for val in values[x]:
            if val in afr:
                type1 = x
                val1 = val
                done = True
        if done:
            break

    dom_per_var[val1] = [4]
    dom_per_var_p[val1] = [4]

    return []

def make_dir_const(word, afr):
    rv = ""
    lv = ""

    if word == "right":
        right_part = afr.split("right")[0]
        left_part = afr.split("right")[1]
    else:
        right_part = afr.split("left")[1]
        left_part = afr.split("left")[0]

    done = False
    for x in values:
        for val in values[x]:
            if val in right_part:
                rv = val
                done = True
        if done:
            break

    done = False
    for x in values:
        for val in values[x]:
            if val in left_part:
                lv = val
                done = True
        if done:
            break

    dom_per_var[lv].remove(4)
    dom_per_var[rv].remove(0)
    dom_per_var_p[lv].remove(4)
    dom_per_var_p[rv].remove(0)

    return [[rv, lv], right_constraint]

def make_next_const(word, afr):
    rv = ""
    lv = ""

    left_part = afr.split(word)[0]
    right_part = afr.split(word)[1]

    done = False
    for x in values:
        for val in values[x]:
            if val in right_part:
                rv = val
                done = True
        if done:
            break

    done = False
    for x in values:
        for val in values[x]:
            if val in left_part:
                lv = val
                done = True
        if done:
            break

    return [[lv, rv], next_constraint]


def make_special_constr(word, afr):
    if word == "first":
        return make_first_const(afr)
    if word == "middle":
        return make_middle_const(afr)
    if word == "last":
        return make_last_const(afr)
    if word == "right" or word == "left":
        return make_dir_const(word, afr)
    if word == "next":
        return make_next_const(word, afr)

def make_constraints():
    global constraints

    # all 5 have different values for each field
    for category in values.keys():
        current_list = values[category]
        for p in combinations(current_list, 2):
            constraints.append([list(p), different_values])

    # get restrictions from afirmations
    for afr in affirmations:
        done = False
        for word in key_words:
            if word in afr:
                done = True
                if word == "right" or word == "left" or word == "next":
                    constraints.append(make_special_constr(word, afr))
                else:
                    make_special_constr(word, afr)
                break
        if not done:
            constraints.append(make_2_value_constr(afr))

def make_arcs():
    global arcs
    for c in constraints:
        vars = c[0]
        func = c[1]
        tuple1 = copy.deepcopy(vars)
        tuple1.append(func)
        arcs.append(tuple1)
        tuple2 = copy.deepcopy(vars)
        tuple2.append(func)
        tuple2.append("r")
        arcs.append(tuple2)

def get_check_var(arc):
    if arc[len(arc) - 1] == "r":
        return (arc[1], arc[0])
    return (arc[0], arc[1])

def print_dom_vars(mp):
    for k in mp.keys():
        print(k, mp[k])

def arc_reduce(arc):
    change = False
    x, y = get_check_var(arc)
    new_domain = copy.deepcopy(dom_per_var[x])

    for vx in dom_per_var[x]:
        sattisfied = False
        for vy in dom_per_var[y]:
            if arc.index(x) < arc.index(y):
                is_sattisfied = arc[2](vx, vy)
                if is_sattisfied:
                    sattisfied = True
                    break
            else:
                is_sattisfied = arc[2](vy, vx)
                if is_sattisfied:
                    sattisfied = True
                    break

        if not sattisfied:
            new_domain.remove(vx)
            change = True

    dom_per_var[x] = new_domain
    return change

def get_right_side(x):
    ret_arcs = []

    for arc in arcs:
        if x not in arc:
            continue

        if arc.index(x) == 0 and arc[len(arc) - 1] == "r":
            ret_arcs.append(arc)

        if arc.index(x) == 1 and arc[len(arc) - 1] != "r":
            ret_arcs.append(arc)

    return ret_arcs

def ac3():
    worklist = copy.copy(arcs)
    worklist.reverse()

    while len(worklist) != 0:
        current_arc = worklist.pop()
        x, y = get_check_var(current_arc)
        if (arc_reduce(current_arc)):
            if len(dom_per_var[x]) == 0:
                return False
            else:
                next_arcs = get_right_side(x)
                for narc in next_arcs:
                    if narc not in worklist:
                        worklist.append(narc)

    return True

def get_contraints(v1, v2):
    final_constraints = []

    for c in constraints:
        vars = c[0]
        if vars[0] == v1 and vars[1] == v2:
            final_constraints.append(c)
        if vars[1] == v1 and vars[0] == v2:
            final_constraints.append(c)

    return final_constraints

def check_if_ok(solution):
    assigned_variable = solution.keys()

    for p in combinations(assigned_variable, 2):
        list_of_constraints = get_contraints(p[0], p[1])
        for c in list_of_constraints:
            vars = c[0]
            if vars.index(p[0]) < vars.index(p[1]):
                if not c[1](solution[p[0]], solution[p[1]]):
                    return False
            else:
                if not c[1](solution[p[1]], solution[p[0]]):
                    return False

    return True

def print_solution(solution):
    final_sol = [[],[],[],[],[]]

    for var in solution:
        final_sol[solution[var]].append(var)

    for idx,house in enumerate(final_sol):
        print("House" + str(idx) + ": " + str(house))

def solve_problem(solution):
    if not check_if_ok(solution):
        return False

    if len(solution.keys()) == 25:
        return solution

    remaining_vars = [x for x in variables if x not in solution.keys()]

    for value in dom_per_var[remaining_vars[0]]:
        solution[remaining_vars[0]] = value
        rez = solve_problem(solution)
        if rez != False:
            return rez
        del solution[remaining_vars[0]]

    return False

def check_forward(var, solution):
    tnou = {}
    remaining_vars = [x for x in variables if x not in solution.keys()]

    for var2 in remaining_vars:
        list_of_constraints = get_contraints(var, var2)
        if list_of_constraints != []:
            tnou[var2] = []
        else:
            continue
        for val2 in dom_per_var_p[var2]:
            for c in list_of_constraints:
                vars = c[0]
                if vars.index(var) < vars.index(var2):
                    if c[1](solution[var], val2):
                        if val2 not in tnou[var2]:
                            tnou[var2].append(val2)
                else:
                    if c[1](val2, solution[var]):
                        if val2 not in tnou[var2]:
                            tnou[var2].append(val2)

        if var2 in tnou and tnou[var2] == []:
            return None

    return tnou

def check_future(var, tnou, solution):

    if len(solution.keys()) + 1 >= 25:
        return

    # for u1, u+1, n
    for var2 in tnou.keys():
        # for l1 in tnou[u1]
        for val2 in tnou[var2]:
            # for u2, u+1, n, u1!=u2
            for var3 in tnou.keys():

                if var2 != var3:
                    consistent = False
                    list_of_constraints = get_contraints(var2, var3)
                    if list_of_constraints == []:
                        consistent = True
                    #for l2 in tnou[u2]
                    for val3 in tnou[var3]:
                        found = False
                        for c in list_of_constraints:
                            vars = c[0]
                            if vars.index(var2) < vars.index(var3):
                                if c[1](val2, val3):
                                    found = True
                                    break
                            else:
                                if c[1](val3, val2):
                                    found = True
                                    break

                        if found:
                            consistent = True
                            break

                    if not consistent:
                        tnou[var2].remove(val2)
                        break

        if tnou[var2] == []:
            return None

    return tnou


def total_prediction(solution):

    if not check_if_ok(solution):
        return False

    if len(solution.keys()) == 25:
        return solution

    remaining_vars = [x for x in variables if x not in solution.keys()]

    for value in dom_per_var_p[remaining_vars[0]]:
        solution[remaining_vars[0]] = value

        if len(solution.keys()) < 25:
            tnou = check_forward(remaining_vars[0], solution)
            if tnou != None:
                if len(tnou.keys()) >= 2:
                    tnou = check_future(remaining_vars[0], tnou, solution)
                else:
                    tnou = True
                if tnou != None:
                    rez = total_prediction(solution)
                    if rez != False:
                        return rez
                    del solution[remaining_vars[0]]
                else:
                    del solution[remaining_vars[0]]
            else:
                del solution[remaining_vars[0]]
        else:
            rez = total_prediction(solution)
            if rez != False:
                return rez
            del solution[remaining_vars[0]]

    return False

def get_answer_to_questions(solution):
    variable = ""

    done = False
    for x in values:
        for val in values[x]:
            if val in question:
                variable = val
                done = True
        if done:
            break

    print("Answer: " + variable + " is in house " + str(solution[variable]))
    print()


def solve_using_complete_prediction():
    print("Solving with complete prediction!\n")
    sol = total_prediction({})
    print_solution(sol)
    get_answer_to_questions(sol)

def solve_using_ac3():
    # reduce domains
    print("Solve using ac3!\n")
    possible = ac3()

    if not possible:
        print("Solution not possible")

    # calculate solution
    sol = solve_problem({})
    print_solution(sol)
    get_answer_to_questions(sol)


def main():
    read_input()
    make_all_variables()
    make_constraints()
    make_arcs()

    if len(sys.argv) < 3:
        print("main.py file ac3/pred")
        return

    if sys.argv[2] == "ac3":
        solve_using_ac3()
    elif sys.argv[2] == "pred":
        solve_using_complete_prediction()
    else:
        solve_using_ac3()
        solve_using_complete_prediction()

if __name__ == "__main__":
    main()