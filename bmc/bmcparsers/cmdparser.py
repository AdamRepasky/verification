#!/usr/bin/python

from os.path import join

def parse_cmd():
    from argparse import ArgumentParser
    from os.path import isfile

    parser = ArgumentParser(description='Process some integers.')
    parser.add_argument('--maxk', type=int,
                        help='The bound (the max value of k to try)')
    parser.add_argument('--init',
                        help='Path to a file containing a initial relation formula')
    parser.add_argument('--trans',
                        help='Path to a file containing a transition relation formula')
    parser.add_argument('--prp',
                        help='Path to a file containing a property relation formula')
    parser.add_argument('--vars',
                        help='Path to a file containing two lines with a space-separated '\
                             'list of names of variables used in the formulas. The first '\
                             'line are current-state variables and the second line are '\
                             'the next-state variables')
    parser.add_argument('--backward', action='store_const', const=True,
                        default=False, help='Perform backward checks.')
    parser.add_argument('--completeness', action='store_const', const=True,
                        default=False, help='Perform completeness checks.')
    parser.add_argument('--system',
                        help='Path to a directory containing files init.txt, '\
                             'trans.txt, vars.txt that describe the system. '\
                             'Overriden by --trans, --init, and --vars.')

    parser.add_argument('--dot', default=None,
                        help='Dump the system into .dot file given in this argument.')


    args = parser.parse_args()

    if args.system:
        if args.init is None:
            args.init = join(args.system, 'init.txt')
        if args.trans is None:
            args.trans = join(args.system, 'trans.txt')
        if args.vars is None:
            args.vars = join(args.system, 'vars.txt')

    if args.trans is None:
        raise AssertionError("Transition relation not given")
    if args.vars is None:
        raise AssertionError("Variables not given")
    if args.init is None:
        raise AssertionError("Init relation not given")
    if args.prp is None:
        if args.system:
            args.prp = join(args.system, 'prp.txt')
            if isfile(args.prp):
                print("No prp file given, using 'prp.txt' from the system directory. Override by --prp")
            else:
                raise AssertionError("Property formula not given")
        else:
            raise AssertionError("Property formula not given")

    if args.maxk:
        args.maxk = int(args.maxk)

    if not isfile(args.trans):
        raise OSError("File {0} does not exists".format(args.trans))
    if not isfile(args.init):
        raise OSError("File {0} does not exists".format(args.init))
    if not isfile(args.prp):
        raise OSError("File {0} does not exists".format(args.prp))

    return args


