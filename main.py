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
dom_per_var = {}
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
    for typeVar in attributes:
        for i in range(5):
            variables.append(typeVar + str(i))
            dom_per_var[typeVar + str(i)] = copy.deepcopy(values[typeVar])

def value_constraint(v, x0):
    return v == x0

def diff_value_constraint(v, x0):
    return v != x0

def different_values(x0, x1):
    return x0 != x1

def two_values_constraint(v1,v2,x0=0,x1=0,x2=0,x3=0,x4=0,x5=0,x6=0,x7=0,x8=0,x9=0):
    if x0 == v1 and x1 == v2:
        return True
    if x2 == v1 and x3 == v2:
        return True
    if x4 == v1 and x5 == v2:
        return True
    if x6 == v1 and x7 == v2:
        return True
    if x8 == v1 and x9 == v2:
        return True
    return False

def right_constraint(v1,v2,x0=0,x1=0,x2=0,x3=0,x4=0,x5=0,x6=0,x7=0,x8=0,x9=0):
    if x0 == v1 and x1 == v2:
        return True
    if x2 == v1 and x3 == v2:
        return True
    if x4 == v1 and x5 == v2:
        return True
    if x6 == v1 and x7 == v2:
        return True
    if x8 == v1 and x9 == v2:
        return True
    return False

def next_constraint(v1,v2,x0=0,x1=0,x2=0,x3=0,x4=0,x5=0,x6=0,x7=0,x8=0,x9=0):
    if x0 == v1 and x1 == v2:
        return True
    if x2 == v1 and x3 == v2:
        return True
    if x4 == v1 and x5 == v2:
        return True
    if x6 == v1 and x7 == v2:
        return True
    if x8 == v1 and x9 == v2:
        return True
    return False

def make_2_value_constr(afr):
    type1 = ""
    type2 = ""
    val1 = ""
    val2 = ""
    done = False

    for x in values:
        for val in values[x]:
            if val in afr:
                if type1 == "" :
                    type1 = x
                    val1 = val
                else:
                    type2 = x
                    val2 = val
                    done = True
        if done:
            break

    current_constraint_vars = []
    for x in range(5):
        current_constraint_vars.append(type1 + str(x))
        current_constraint_vars.append(type2 + str(x))

    return [current_constraint_vars, functools.partial(two_values_constraint, val1, val2)]

def make_first_const(afr):
    type1 = ""
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

    variable = type1 + "0"

    dom_per_var[variable] = [val1]

    return [[variable], functools.partial(value_constraint, val1)]

def make_middle_const(afr):
    type1 = ""
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

    variable = type1 + "2"

    dom_per_var[variable] = [val1]

    return [[variable], functools.partial(value_constraint, val1)]

def make_last_const(afr):
    type1 = ""
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

    variable = type1 + "4"

    dom_per_var[variable] = [val1]

    return [[variable], functools.partial(value_constraint, val1)]

def make_dir_const(word, afr):
    rt = ""
    rv = ""
    lt = ""
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
                rt = x
                rv = val
                done = True
        if done:
            break

    done = False
    for x in values:
        for val in values[x]:
            if val in left_part:
                lt = x
                lv = val
                done = True
        if done:
            break

    constraints_to_add = []

    constraints_to_add.append([[lt + "4"], functools.partial(diff_value_constraint, lv)])
    constraints_to_add.append([[rt + "0"], functools.partial(diff_value_constraint, rv)])
    dom_per_var[lt + "4"].remove(lv)
    dom_per_var[rt + "0"].remove(rv)

    current_vars = []
    for x in range(4):
        current_vars.append(lt + str(x))
        current_vars.append(rt + str(x + 1))

    constraints_to_add.append([current_vars, functools.partial(right_constraint, lv, rv)])

    return constraints_to_add

def make_next_const(word, afr):
    rt = ""
    rv = ""
    lt = ""
    lv = ""

    left_part = afr.split(word)[0]
    right_part = afr.split(word)[1]

    done = False
    for x in values:
        for val in values[x]:
            if val in right_part:
                rt = x
                rv = val
                done = True
        if done:
            break

    done = False
    for x in values:
        for val in values[x]:
            if val in left_part:
                lt = x
                lv = val
                done = True
        if done:
            break

    constraints_to_add = []

    current_vars = []
    for x in range(4):
        current_vars.append(lt + str(x))
        current_vars.append(rt + str(x + 1))

    constraints_to_add.append([current_vars, functools.partial(next_constraint, lv, rv)])

    current_vars = []
    for x in range(4):
        current_vars.append(rt + str(x))
        current_vars.append(lt + str(x + 1))

    constraints_to_add.append([current_vars, functools.partial(next_constraint, rv, lv)])

    return constraints_to_add


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
    for p in combinations(variables, 2):
        if p[0][:-1] == p[1][:-1]:
            constraints.append([list(p), different_values])

    # get restrictions from afirmations
    for afr in affirmations:
        done = False
        for word in key_words:
            if word in afr:
                done = True
                if word == "right" or word == "left" or word == "next":
                    constraints.extend(make_special_constr(word, afr))
                else:
                    constraints.append(make_special_constr(word, afr))
                break
        if not done:
            constraints.append(make_2_value_constr(afr))

def getRelatedConstraints(x):
    related_constraints = []
    for c in constraints:
        vars = c[0]
        if x in vars:
            related_constraints.insert(0, c)
    return related_constraints

def arc_reduce(c, x):
    change = False
    x_index = c[0].index(x)
    for vx in dom_per_var[x]:
        possible_vars = copy.deepcopy(c[0])
        possible_vars.remove(x)
        for var in possible_vars:
            for vy in dom_per_var[var]:
                x_index = "x" + str(c[0].index(x))
                y_index = "x" + str(c[0].index(var))
                f_call_str = 'c[1](' + x_index + '="' + vx + '",' + y_index + '="' + vy + '")'
                constraint_value = eval(f_call_str)
                print(f_call_str, constraint_value)
                input()

def ac3():
    for x in variables:
        worklist = getRelatedConstraints(x)

        while len(worklist) != 0:
            current_constr = worklist.pop()
            arc_reduce(current_constr, x)




def main():
    read_input()
    make_all_variables()
    make_constraints()
    for x in constraints:
        print(x)
    print("START AC#")
    ac3()

if __name__ == "__main__":
    main()