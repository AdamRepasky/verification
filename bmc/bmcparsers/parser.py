#!/usr/bin/python

def _check_validname(name):
    l = len(name)
    assert l > 0, "Empty name not allowed"
    assert (name[0] == '!' and l > 1 and name[1].isalpha()) or\
           (name[0].isalpha() and (l == 1 or name[1:].isalnum())),\
           "Wrong variable name: '{0}'. First letter of a name must by a letter,"\
           " the rest letters and digits. The name may be prefixed with !.".format(name)

def _parse_name(name):
    _check_validname(name)

    negated = False
    if name[0] == '!':
        return name[1:], True

    return name, False

class Variables:
    def __init__(self):
        # lists of current state variables and next-state variables
        # (next-state variable of xs[i] is xns[i]
        self.xs = []
        self.xns = []
        # mapping of names to variables
        self.allVars = {}

class Parser:
    def __init__(self):
        pass

    def createVariable(self, name):
        raise NotImplementedError("Must be overridden")

    def createAnd(self, *args):
        raise NotImplementedError("Must be overridden")

    def createOr(self, *args):
        raise NotImplementedError("Must be overridden")

    def createNot(self, arg):
        raise NotImplementedError("Must be overridden")

    def parseVariables(self, path):
        """
        \param path is a path to a file that contains two comma-separated
        list of variables, each on its own line,
        The first line (list) are names of (boolean) variables
        and the second list are names of next-state variables.
        E.g.,

        a b c
        an ab ac

        \return Variables object
        """

        lxs, lxns = None, None
        with open(path, 'r') as f:
            for line in f:
                sline = line.strip()
                if not sline:
                    continue
                if lxs:
                    lxns = sline
                    break
                else:
                    assert lxns is None
                    lxs = sline

        assert lxs and lxns

        V = Variables()

        for x in lxs.split():
            x = x.strip()
            assert V.allVars.get(x) is None, "Duplicated name of a variable: " + x
            v = self.createVariable(x)
            V.xs.append(v)
            V.allVars[x] = v

        for x in lxns.split():
            x = x.strip()
            assert V.allVars.get(x) is None, "Duplicated name of a variable: " + x
            v = self.createVariable(x)
            V.xns.append(v)
            V.allVars[x] = v

        assert len(V.xs) == len(V.xns),\
               "A different number of variables and next-state variables"

        return V



    def parseFormula(self, path, V):
        """
        Parse a file with a formula and return the formula
        as Z3 objects.
        \param path is a path to the file with the formula
        \params xs, xns contain the variables parsed with parseVariables
        """
        try:
            return self._parse(path, V)
        except ValueError as e:
            from sys import stderr
            stderr.write(str(e))
            stderr.write('\n')
            return None

    def parseSystem(self, variables, init, trans):
        """
        Wrapper around parseVariables and parseFormula
        \param variables  path to a file with variables
        \param init       path to a file with init formula
        \param trans      path to a file with transition formula
        \return           variables,
                          init formula,
                          transition formula
        """
        V = self.parseVariables(variables)
        initF = self.parseFormula(init, V)
        transF = self.parseFormula(trans, V)
        return V, initF, transF

    def _parse_line(self, V, line):
        literals = []
        variables = line.split()
        for v in variables:
            var, negated = _parse_name(v)
            smtVar = V.allVars.get(var)
            if smtVar is None:
                raise ValueError("Unknown variable: {0}".format(var))

            if negated:
                literals.append(self.createNot(smtVar))
            else:
                literals.append(smtVar)

        return self.createOr(literals)

    def _parse(self, path, V):
        disjuncts = []

        with open(path, 'r') as f:
            for line in f:
                disjuncts.append(self._parse_line(V, line))

        return self.createAnd(*disjuncts)

