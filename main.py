
from pcfg import PRule, PCFG

def main():
    GRAMMAR_FILE = "grammar.txt"
    DATA_FILE = "data.txt"

    file_grammar = open(GRAMMAR_FILE, "r")
    lines = file_grammar.read().splitlines()

    start_index = lines.index("# Start Symbol #")+2
    grammar_index = lines.index("# Grammar #")+2
    lexicon_index = lines.index("# Lexicon #")+2

    start_variable = lines[start_index].split()[1]

    grammar_rules = {}
    for i in range(grammar_index, lexicon_index-3):
        split_line = lines[i].split()
        n = len(split_line)
        if n != 0:
            variable = split_line[0]
            derivation = split_line[2:-1]
            prob = split_line[-1].replace("[", "").replace("]", "")
            rule = PRule(variable, derivation, prob)
            if variable not in grammar_rules:
                grammar_rules[variable] = []
            grammar_rules[variable].append(rule)

    for i in range(lexicon_index, len(lines)):
        split_line = lines[i].split()
        variable = split_line[0]
        derivations = split_line[2:]
        for j in range(0, len(derivations), 3):
            der = derivations[j].replace('"', "")
            prob = derivations[j+1].replace("[", "").replace("]", "")
            rule = PRule(variable, (der,), prob)
            if variable not in grammar_rules:
                grammar_rules[variable] = []
            grammar_rules[variable].append(rule)

    pcfg = PCFG(start_variable, grammar_rules)
    near_cnf, changes = pcfg.to_near_cnf()

    file_data = open(DATA_FILE, "r")
    data_lines = file_data.read().splitlines()
    for line in data_lines:
        if line != '':
            res = near_cnf.cky_parser(line)
            if res is None:
                print(line + ": cannot be generate by this grammar")
            else:
                print("near cnf tree: ", res)
                print("original tree: ", near_cnf.adjust_near_cnf_ptree(res, changes))
                print("---------------------")


if __name__ == '__main__':
    main()
