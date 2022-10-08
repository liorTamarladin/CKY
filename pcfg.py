import copy
from itertools import chain, combinations
from collections import defaultdict

from ptree import PTree, Node

EPSILON = 'EPSILON'


class PRule(object):
    def __init__(self, variable, derivation, probability):
        self.variable = str(variable)
        if derivation != EPSILON:
            self.derivation = tuple(derivation)
        else:
            self.derivation = (EPSILON,)
        self.probability = float(probability)

    def derivation_length(self):
        return len(self.derivation)

    def __repr__(self):
        compact_derivation = " ".join(self.derivation)
        return self.variable + ' -> ' + compact_derivation + ' (' + str(self.probability) + ')'

    def __eq__(self, other):
        try:
            return self.variable == other.variable and self.derivation == other.derivation
        except:
            return False


class PCFG(object):
    def __init__(self, start_variable='S', rules = None):
        if rules is None:
            self.rules = {}
        else:
            self.rules = copy.deepcopy(rules) # A dictionary that maps an str object to a list of PRule objects
        self.start = start_variable # Start symbol of the grammar

    def add_rule(self, rule):
        '''
        Adds a rule to dictionary of rules in grammar.
        '''
        if rule.variable not in self.rules:
            self.rules[rule.variable] = []
        self.rules[rule.variable].append(rule)

    def remove_rule(self, rule):
        '''
        Removes a rule from dictionary of rules in grammar.
        '''
        try:
            self.rules[rule.variable].remove(rule)
        except KeyError:
            pass
        except ValueError:
            pass

    def to_near_cnf(self):
        """
        Returns an equivalent near-CNF grammar.
        """
        change = defaultdict(list)

        # 1
        count = 0
        s = f'S{count}'
        while s in self.variables():
            count += 1
            s = f'S{count}'
        near_cnf = PCFG(start_variable=s, rules=self.rules)
        near_cnf.add_rule(PRule(near_cnf.start, (self.start,), 1))

        first_change = PCFGChange(PRule(near_cnf.start, (self.start,), 1), PCFGChange.NEW_START, 'ADD')
        change[first_change.rule.variable].append(first_change)

        # 2
        for rule in list(near_cnf.all_rules()):
            if rule.variable != near_cnf.start and EPSILON in rule.derivation:
                # a
                near_cnf.remove_rule(rule)

                if rule.variable == self.start and rule.derivation_length() == 1:
                    new_rule = PRule(near_cnf.start, EPSILON, rule.probability)
                    near_cnf.add_rule(new_rule)
                    change[new_rule.variable].append(PCFGChange(new_rule, PCFGChange.EPSILON_RULE, rule))

                # b
                for r in near_cnf.rules[rule.variable]:
                    p = rule.probability
                    q = r.probability
                    r.probability = (q / (1-p))

                # c
                for r in list(near_cnf.all_rules()):
                    if rule.variable in r.derivation:
                        p = rule.probability
                        q = r.probability
                        m = r.derivation.count(rule.variable)

                        if r.derivation_length() == 1 and rule.variable == r.variable == r.derivation[0] == self.start:
                            new_rule = PRule(near_cnf.start, EPSILON, rule.probability)
                            if near_cnf.find_rule(new_rule) is None:
                                near_cnf.add_rule(new_rule)
                                change[new_rule.variable].append(PCFGChange(new_rule, PCFGChange.EPSILON_RULE, r))

                        else:
                            r.probability = q * ((1-p) ** m)

                            for applied_rule, k in near_cnf.apply_removed_rule(r, rule.variable):
                                if len(applied_rule) != 0:
                                    probability = q * (p ** k) * ((1-p) ** (m-k))

                                    found_rule = near_cnf.find_rule(applied_rule)
                                    if found_rule is not None:
                                        found_rule.probability += probability
                                    else:
                                        new_rule = PRule(r.variable, applied_rule, probability)
                                        near_cnf.add_rule(new_rule)
                                        change[new_rule.variable].append(PCFGChange(new_rule, PCFGChange.EPSILON_RULE, r))

        near_cnf = near_cnf.clean_rules()

        # 3a
        count = 0
        while any(r.derivation_length() > 2 for r in list(near_cnf.all_rules())):
            for rule in list(near_cnf.all_rules()):
                if rule.derivation_length() > 2:
                    n1 = f'N{count}'
                    while n1 in self.variables():
                        count += 1
                        n1 = f'N{count}'
                    new_rule_1 = PRule(rule.variable, (rule.derivation[0], n1), rule.probability)
                    new_rule_2 = PRule(n1, rule.derivation[1:], 1)

                    near_cnf.add_rule(new_rule_1)
                    near_cnf.add_rule(new_rule_2)
                    near_cnf.remove_rule(rule)

                    change[new_rule_1.variable].append(PCFGChange(new_rule_1, PCFGChange.AUXILIARY, 'ADD'))
                    change[new_rule_2.variable].append(PCFGChange(new_rule_2, PCFGChange.AUXILIARY, 'ADD'))

                    count += 1
        near_cnf = near_cnf.clean_rules()

        # 3b
        for rule in list(near_cnf.all_rules()):
            if rule.derivation_length() == 2 and any(near_cnf.is_terminal(c) for c in rule.derivation):
                d1, d2 = rule.derivation

                if near_cnf.is_terminal(d1) and not near_cnf.is_terminal(d2):
                    y = f'N{count}'
                    while y in self.variables():
                        count += 1
                        y = f'Y{count}'
                    near_cnf.add_rule(PRule(rule.variable, [y, d2], rule.probability))
                    near_cnf.add_rule(PRule(y, [d1], 1))

                    change[rule.variable].append(PCFGChange(PRule(rule.variable, [y, d2], rule.probability), PCFGChange.AUXILIARY, 'ADD'))
                    change[y].append(PCFGChange(PRule(y, [d1], 1), PCFGChange.AUXILIARY, 'ADD'))

                elif not near_cnf.is_terminal(d1) and near_cnf.is_terminal(d2):
                    y = f'N{count}'
                    while y in self.variables():
                        count += 1
                        y = f'Y{count}'
                    near_cnf.add_rule(PRule(rule.variable, [d1, y], rule.probability))
                    near_cnf.add_rule(PRule(y, [d2], 1))

                    change[rule.variable].append(PCFGChange(PRule(rule.variable, [d1, y], rule.probability), PCFGChange.AUXILIARY, 'ADD'))
                    change[y].append(PCFGChange(PRule(y, [d2], 1), PCFGChange.AUXILIARY, 'ADD'))

                else:
                    y1 = f'N{count}'
                    while y1 in self.variables():
                        count += 1
                        y1 = f'Y{count}'
                    count += 1
                    y2 = f'Y{count}'
                    while y2 in self.variables():
                        count += 1
                        y2 = f'Y{count}'

                    near_cnf.add_rule(PRule(rule.variable, [y1, y2], rule.probability))
                    near_cnf.add_rule(PRule(y1, [d1], 1))
                    near_cnf.add_rule(PRule(y2, [d2], 1))

                    change[rule.variable].append(PCFGChange(PRule(rule.variable, [y1, y2], rule.probability), PCFGChange.AUXILIARY, 'ADD'))
                    change[y1].append(PCFGChange(PRule(y1, [d1], 1), PCFGChange.AUXILIARY, 'ADD'))
                    change[y2].append(PCFGChange(PRule(y2, [d2], 1), PCFGChange.AUXILIARY, 'ADD'))

                count += 1
                near_cnf.remove_rule(rule)

        near_cnf = near_cnf.clean_rules()
        return near_cnf, change

    def all_rules(self):
        return chain(*self.rules.values())

    def clean_rules(self):
        '''
        removed rules with probability 0.
        '''
        for rule in list(self.all_rules()):
            if rule.probability == 0.0:
                self.remove_rule(rule)
        return self

    @staticmethod
    def apply_removed_rule(rhs_rule, removed_rule_variable):
        """
        Returns all rules that can be obtained by applying the removed rule
        partially or fully.

        From the PDF:
        rhs_rule is B
        removed_rule_variable is A
        """
        obtained_rules = []
        m = rhs_rule.derivation.count(removed_rule_variable)

        for k in range(1, m + 1):
            for obtained_rule in combinations(rhs_rule.derivation, rhs_rule.derivation_length() - k):
                if obtained_rule.count(removed_rule_variable) == m - k:
                    obtained_rules.append((obtained_rule, k))

        return obtained_rules

    def find_rule(self, other):
        for rule in list(self.all_rules()):
            if rule == other:
                return rule

        return None

    def variables(self):
        """
        Returns V
        """
        return list(self.rules.keys())

    def is_terminal(self, c):
        """
        Returns whether c is in Σ
        """
        return c not in self.variables()

    def cky_parser(self, string):
        '''
        Parses the input string given the grammar, using the probabilistic CKY algorithm.
        If the string has been generated by the grammar - returns a most likely parse tree for the input string.
        Otherwise - returns None.
        The CFG is given in near-CNF.
        '''

        # 1
        words = [''] + string.split()
        n = len(words) - 1
        t = [[{} for _ in range(n+1)] for _ in range(n+1)]
        nodes = [[{} for _ in range(n+1)] for _ in range(n+1)]

        # in case of an empty string input
        if len(words) == 1 and words[0] == '':
            check_rule = PRule(self.start, EPSILON, 1)
            if check_rule in self.all_rules():
                prob = self.find_rule(check_rule).probability
                if prob < (2 ** -50):
                    return None
                else:
                    tree = PTree(Node(self.start, [Node(EPSILON, [])]), prob)
                    return tree

        # 2

        for j in range(1, n+1):
            for rule in list(self.all_rules()):
                if words[j] in rule.derivation:
                    A = rule.variable
                    t[j-1][j][A] = rule.probability
                    nodes[j-1][j][A] = Node(A, [Node(words[j], [])])

            bool_while = True
            while bool_while:
                bool_while = False
                for rule in list(self.all_rules()):
                    if rule.derivation_length() == 1:
                        A = rule.variable
                        B = rule.derivation[0]
                        if t[j - 1][j].get(A, 0) < rule.probability * t[j - 1][j].get(B, 0):
                            t[j - 1][j][A] = rule.probability * t[j - 1][j][B]
                            nodes[j - 1][j][A] = Node(A, [nodes[j - 1][j][B]])
                            bool_while = True
            # 3

            for i in range(j-2, -1, -1):
                for k in range(i+1, j):
                    for rule in list(self.all_rules()):
                        if rule.derivation_length() == 2:
                            A = rule.variable
                            B, C = rule.derivation
                            if t[i][j].get(A, 0) < rule.probability * t[i][k].get(B, 0) * t[k][j].get(C, 0):
                                t[i][j][A] = rule.probability * t[i][k][B] * t[k][j][C]
                                nodes[i][j][A] = Node(A, [nodes[i][k][B], nodes[k][j][C]])

                    bool_while = True
                    while bool_while:
                        bool_while = False
                        for rule in list(self.all_rules()):
                            if rule.derivation_length() == 1:
                                A = rule.variable
                                B = rule.derivation[0]
                                if t[i][j].get(A, 0) < rule.probability * t[i][j].get(B, 0):
                                    t[i][j][A] = rule.probability * t[i][j][B]
                                    nodes[i][j][A] = Node(A, [nodes[i][j][B]])
                                    bool_while = True

        if t[0][n].get(self.start, 0) < (2 ** -50):
            return None

        return PTree(nodes[0][n][self.start], t[0][n][self.start])

    def is_valid_grammar(self):
        '''
        Validates that the grammar is legal (meaning - the probabilities of the rules for each variable sum to 1).
        '''
        V = self.variables()
        for variable in V:
            sum_prob = 0
            for rule in list(self.all_rules()):
                if rule.variable == variable:
                    sum_prob += rule.probability
            if abs(1 - sum_prob) > 0.0001:
                return False
        return True

    def adjust_near_cnf_ptree(self, ptree, changes):
        '''
        THIS METHOD IS RELEVANT ONLY FOR THE BONUS QUSETION.
        Adjusts a PTree derived by a grammar converted to near-CNF, to the equivalent PTree of the original grammar.
        '''
        # TODO implement this method (for the bonus question)

        def rec_adjust_near_cnf_ptree(ptree, curr_node, changes, parent):

            if len(curr_node.children) == 1: #meaning having 1 child
                rec_adjust_near_cnf_ptree(ptree, curr_node.children[0], changes, curr_node)

            if len(curr_node.children) == 2: #meaning having 2 children
                rec_adjust_near_cnf_ptree(ptree, curr_node.children[0], changes, curr_node)
                rec_adjust_near_cnf_ptree(ptree, curr_node.children[1], changes, curr_node)

            if len(curr_node.children) != 0:
                if curr_node.key in changes:
                    is_changed = True
                    while is_changed:
                        is_changed = False
                        for r in changes[curr_node.key]:
                            der = []
                            for child in curr_node.children:
                                der.append(child.key)
                            curr_rule = PRule(curr_node.key, der, 1)
                            if curr_rule == r.rule:
                                change_type = r.change_type
                                if change_type == 'new_start':
                                    ptree.root = curr_node.children[0]
                                elif change_type == 'auxiliary':
                                    if r.rule.probability == 1:
                                        for c in curr_node.children:
                                            if len(curr_node.children) == 2:
                                                try:
                                                    parent.children.remove(curr_node)
                                                except:
                                                    pass
                                                parent.children.append(c)
                                            elif len(c.children) == 0:
                                                curr_node.key = c.key
                                                curr_node.children = []
                                elif change_type == 'epsilon_rule':
                                    cnt = 0
                                    for d in r.info.derivation:
                                        if len(r.rule.derivation) > cnt and d == r.rule.derivation[cnt]:
                                            cnt += 1
                                        else:
                                            if self.is_terminal(d):
                                                curr_node.children.insert(cnt, Node(d, []))
                                            else:
                                                curr_node.children.insert(cnt, Node(d, [Node(EPSILON, [])]))
                                            is_changed = True
        if ptree == None:
            print("the tree is None, cannot convert")
            return None
        rec_adjust_near_cnf_ptree(ptree, ptree.root, changes, parent=None)

        return ptree


class PCFGChange(object):
    NEW_START = 'new_start'
    EPSILON_RULE = 'epsilon_rule'
    AUXILIARY = 'auxiliary'

    def __init__(self, rule, change_type, info=None):
        '''
        THIS CLASS IS RELEVANT ONLY FOR THE BONUS QUSETION.
        Documents the specific change done on a PCFG.
        '''
        assert change_type in (PCFGChange.NEW_START, PCFGChange.EPSILON_RULE, PCFGChange.AUXILIARY)
        self.rule: PRule = rule
        self.change_type: PRule = change_type
        self.info: PRule = info


