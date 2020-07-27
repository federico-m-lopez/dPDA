#!/usr/bin/env python3
# -*- coding: utf-8 -*-

###############################################################
#  Learning dPDA from examples by constraint solving via SMT  #
###############################################################

# python3 dpda.py
# python3 -m unittest dpda.py

import z3

import base64
import random
import itertools

###############
#  Utilities  #
###############

def unescape(bs):
    try:
        result = bs.decode('unicode_escape').encode('latin-1')
        return result
    except UnicodeDecodeError as e:
        print ("error", e)
        return None

# C'mon, python, seriously?
class List(list):
    def __hash__(self):
        return hash(tuple(self))

# Missing from Z3py:
def Sequence(name, ctx=None):
    """Return a sequence constant named `name`. If `ctx=None`, then the global context is used.
    >>> x = Sequence('x')
    """
    ctx = z3.get_ctx(ctx)
    int_sort = z3.IntSort(ctx)
    return z3.SeqRef(
        z3.Z3_mk_const(ctx.ref(),
                       z3.to_symbol(name, ctx),
                       z3.SeqSortRef(z3.Z3_mk_seq_sort(int_sort.ctx_ref(), int_sort.ast)).ast),
        ctx)

def shortlex(alphabet, prefix=b''):
    """
    Enumerate all strings over alphabet in shortlex order
    """
    assert(len(alphabet))

    iters = []

    for a in alphabet:
        iters += [shortlex(alphabet, prefix=prefix+bytes([a]))]

    yield prefix

    while iters != []:
        for x in iters:
            try:
                yield next(x)
            except StopIteration:
                iters.remove(x)

class InfoTrie:
    """
    A word trie with information optionally attached to nodes
    (self.info == None indicates that the node is an inner node)
    @note only add is supported, not remove
    """
    def __init__(self):
        self.dict = {}
        self.info = None

    def add(self, s, info=True, accum=b''):
        """
        Adds a word, with info.
        Modifies the structure.
        @return the added suffix.
        """
        if len(s):
            i = InfoTrie()
            t = self.dict.setdefault(s[0], i)
            if t == i:
                accum += bytes([s[0]])
            return t.add(s[1:], info, accum)
        else:
            self.info = info
            return accum

    def get(self, s):
        """
        @return None if no info or no path
        """
        if len(s):
            t = self.dict.get(s[0])
            if t != None:
                return t.get(s[1:])
            return None
        return self.info

    def iter(self, prefix=b''):
        """
        @return iterate over the trie, depth-first, outputting all nodes.
        @param prefix optional
        """
        yield (prefix, self, self.info, self.has_children())
        for (k,v) in self.dict.items():
            yield from v.iter(b"%s%s" % (prefix, bytes([k])))

    def has_children(self):
        """
        Assuming the invariant that only inner nodes have info == None,
        this means the node has descendants with info != None
        """
        return len(self.dict) > 0

    def first_word_not_in(self, alphabet):
        '''
        (by shortlex)
        '''
        return next(itertools.filterfalse(lambda w: self.get(w) != None, shortlex(alphabet)))


class Automaton:
    """
    Class for a specific type of real-time deterministic pushdown automata (dPDA)
    Acceptance criterion: stack empty or contaning just a "final state" symbol
    """
    def __init__(self):
        self.QF = set()
        self.D  = dict()
        self.productive = None

    def construct_from_z3_model(self, m, d, Qf, alphabet):
        to_check = [0]
        checked = set(to_check)

        print ("Extracting tables")
        
        self.D  = dict()
        self.QF = set()
        self.productive = None
        
        print ("m[d]  = %s" %  m[d])
        print ("m[qf] = %s" %  m[Qf])

        symbols = set([0])

        while len(to_check):
            current = to_check.pop()
            conf = z3.Unit(z3.IntVal(current))
            
            for a in alphabet: # range(0, 256):
                y = m.evaluate(
                    d(
                        # z3.SubSeq(conf, z3.Length(conf)-1, 1),
                        conf,
                        z3.StringVal(bytes([a]))),
                    model_completion = True)

                def extract_seq_as_list(y):
                    result = List()
                    for c in y.children():
                        if isinstance(c, z3.SeqRef):
                            result += extract_seq_as_list(c)
                        else:
                            result += List([c.as_long()])
                    return result
                            
                rhs = extract_seq_as_list(y)

                for symbol in rhs:
                    symbols.add(symbol)
                
                Dq = self.D.setdefault(current, dict())
                Dq[a] = rhs

                for i in rhs:
                    if not i in checked:
                        checked.add(i)
                        to_check += [i]

        if m.evaluate(Qf(z3.Empty(z3.SeqSort(z3.IntSort())))):
            self.QF.add(List([]))

        print("(stack/q) symbols encountered: %s" % symbols)

        for symbol in symbols:
            conf = z3.Unit(z3.IntVal(symbol))
            f = m.evaluate(Qf(conf))
            if f:
                self.QF.add(List([symbol]))

        self.symbols = symbols

    def productivity(self):
        if self.productive == None:
            self.compute_productivity()
        return self.productive

    def compute_productivity(self):
        """
        Determine for each stack/state symbol whether it leads to QF, or to decreasing length
        """
        productive = {'down':set(), 'toqf':set(), 'tononqf':set()}
        
        S = set()
        
        for k in self.D.keys():
            S.add(k)
        down_immediate = set()
        for s in S:
            if any(map(lambda x: len(x)<1, self.D.get(s).values())):
                down_immediate.add(s)
        toqf_immediate = set()
        for s in S:
            if List([s]) in self.QF:
                toqf_immediate.add(s)

        tononqf_immediate = set()
        for s in S:
            if List([s]) not in self.QF:
                tononqf_immediate.add(s)
                
        import copy
        eqs = copy.deepcopy(self.D)
        changed = True # iterate until no more changes
        down = down_immediate.copy()
        toqf = toqf_immediate.copy()
        tononqf = tononqf_immediate.copy()

        while changed:
            changed = False
            for s in eqs.keys():
                for (k,v) in eqs[s].items():
                    new = List(filter(lambda x: x not in down, eqs[s][k]))
                    if eqs[s][k] != new:
                        changed = True
                    eqs[s][k] = new
                    if new == []:
                        down.add(s)

                    if len(v) == 1 and v[0] in toqf and s not in toqf:
                        toqf.add(s)
                        changed = True

                    if len(v) == 1 and v[0] in tononqf and s not in tononqf:
                        tononqf.add(s)
                        changed = True

                    if len(v) > 1 and s not in tononqf:
                        tononqf.add(s)
                        changed = True

        productive['down'] = down
        productive['toqf'] = toqf
        productive['tononqf'] = tononqf
        self.productive = productive # cache
        return productive


    def enumerate_words(self, alphabet, configurations_prefixes={List([0]) : {b''}}, mode = 'words'):
        """
        Short-Lex enumeration of L (or \Sigma^\ast - L),
        @param trie exclude these words
        """

        successors = {}

        productive = self.productivity()

        for (configuration, prefixes) in configurations_prefixes.items():
            
            # final and empty
            if len(configuration) == 0:
                yield from prefixes
                
            else:
                # final without being empty - the show can go on
                if len(configuration) == 1 and configuration in self.QF:
                    yield from prefixes
                # otherwise, it goes on anyway but the word is not yielded.
                
                # detect empty languages
                if not configuration[-1] in productive["down"]:
                   if not (len(configuration)==1 and configuration[-1] in productive["toqf"]):
                     continue
                 
                # compute next layer
                dmap = self.D.get(configuration[-1])
                if dmap != None:
                    for (a, stack_suffix) in dmap.items():
                        newstack = List(configuration[:-1] + stack_suffix)
                        for prefix in prefixes:
                            successors.setdefault(newstack, set()).add(b"%s%s" % (prefix, bytes([a])))

        if len(successors):
            yield from self.enumerate_words(alphabet, successors, mode)
            


class Automaker:
    """
    attempt to guess "realtime dPDA", (no epsilon moves)
    no explicit set Q of control states, just a stack.
    accept when: A) stack empty or B) stack contains just one symbol from QF
    """
    def __init__(self, t, limitS, limitL):
        self.t = t
        self.s = z3.Solver()
        self.i = 0 # serial number generator
        self.alphabet = range(0, 256)

        # arbitrarily limit number of state/stack symbols
        self.limitS = limitS
        # arbitrarily limit length of added suffix
        self.limitL = limitL


    def set_alphabet(self, alphabet):
        self.alphabet = alphabet

    def addPath(self, prefix, rest, final):
        """
        """
        for l in range(0, len(rest)+1):
            w = prefix + rest[:l]
            sv = b"stack" + base64.b16encode(w)
            self.stackvars[w] = Sequence(sv)

        w = prefix + rest
        self.s_add_finalstate(w, final)
        if len(w):
            self.s_add_transition_to(w)

    def setupProblem(self):
        self.stackvars = {}
        self.Qf = z3.Function("final", z3.SeqSort(z3.IntSort()), z3.BoolSort())
        self.d = z3.Function("delta", z3.SeqSort(z3.IntSort()), z3.StringSort(), z3.SeqSort(z3.IntSort()))
 
        for (w, st, final, has_children) in self.t.iter():

            sv = b"stack" + base64.b16encode(w)
            self.stackvars[w] = Sequence(sv)

            self.s_add_finalstate(w, final)

            if final and has_children:
                self.s_add_nonemptystate(w)

            if len(w):
                self.s_add_transition_to(w)

        self.s.add(self.stackvars[b''] == z3.Unit(z3.IntVal(0)))

        # most useful convention:
        # accept by drained stack, but don't read any more and fail then
        self.s.add(self.Qf(z3.Empty(z3.SeqSort(z3.IntSort()))) == True)

    def s_isFinalWord(self, w):
        z3var = self.stackvars[w]
        return z3.And(z3.Length(z3var)<=1, self.Qf(z3var))

    def s_isFinalConfiguration(self, c):
        z3val = z3.StringVal(c)
        return z3.And(z3.Length(z3val)<=1, self.Qf(z3val))

    def s_add_finalstate(self, w, final=True):
        """
        final=True: the state reached by this word is final     ($w \in L$)
        final=True: the state reached by this word is not final ($w \neg\in L$)
        """
        isFinal = self.s_isFinalWord(w)

        if final:
            self.s.add(isFinal)
        elif final == False:
            self.s.add(z3.Not(isFinal))

    def s_add_nonemptystate(self, w):
        z3var = self.stackvars[w]
        self.s.add(z3.Not(z3.Length(z3var)==0))

    def s_add_transition_to(self, w):
        """
        @pre len(w)>0
        """
        i = self.gennum()
        pre = Sequence("pre%d" % i)
        a = Sequence("a%d" % i)
        
        self.s.add(z3.Length(a) == 1)
        self.s.add(z3.Concat(pre, a) == self.stackvars[w[:-1]])
        x = self.d(a, z3.StringVal(w[-1:]))

        self.s.add(z3.Length(x) <= self.limitL)
        for i in range(self.limitL):
            self.s.add(
                z3.Implies(
                    z3.Length(x) > i,
                    z3.And(
                        x[i] < z3.IntVal(self.limitS),
                        x[i] >= 0)
                ))

        self.s.add(z3.Concat(pre, x) == self.stackvars[w])

    def gennum(self):
        i = self.i
        self.i += 1
        return i

    def askZ3(self):
        r = self.s.check()
        print(r)
        if z3.sat == r:
            self.m = self.s.model()
            self.extract_tables()

            print(self.m)
            return True
        else:
            return False

                
    def extract_tables(self):
        """
        Extract the automaton's information from the Z3 model
        """

        self.automaton = Automaton()
        self.automaton.construct_from_z3_model(self.m, self.d, self.Qf, self.alphabet)
        return self.automaton

    def enumerate_words_t(self, alphabet, prefix=b'', configuration = List([0]), mode = 'words'):
        yield from self.automaton.enumerate_words(alphabet, {configuration : {prefix}}, mode)


################
#  Unit tests  #
################

import unittest

class TrieTest(unittest.TestCase):
    
    def test_trie(self):
        t = InfoTrie()
        self.assertEqual(t.info, None)
        t.add(b'')
        self.assertEqual(t.info, True)
        t.add(b'add')
        self.assertEqual(t.info, True)
        self.assertEqual(t.get(b''), True)
        self.assertEqual(t.get(b'a'), None)
        self.assertEqual(t.get(b'add'), True)
        t.add(b'a')
        self.assertEqual(t.get(b'a'), True)
        t.add(b'ah')
        self.assertEqual(t.get(b'a'), True)
        self.assertEqual(t.get(b'ah'), True)
        self.assertEqual(t.get(b'ad'), None)
        self.assertEqual(len([_ for (_,_,info,_) in t.iter() if info]), 4)
        self.assertEqual(len([_ for (_,_,_,_) in t.iter()]), 5)
        self.assertEqual(len([_ for (_,_,info,_) in t.iter(b'a') if info]), 4)
        self.assertEqual(len([_ for (_,_,_,_) in t.iter(b'a')]), 5)


##################
#  Main program  #
##################

import pprint
import argparse
import fileinput

if __name__=='__main__':
    
    parser = argparse.ArgumentParser( description='realtime-deterministic-PDA constructor', )

    parser.add_argument('-m', action="store", dest="mode", type=str, default="simple")
    parser.add_argument('-i', action="append", dest="files", type=str, default=[])

    parser.add_argument('--version', action='version', version='%(prog)s 0.0.1')

    args = parser.parse_args()
    
    files = args.files
    mode  = args.mode

    try:
        t = InfoTrie()

        # arbitrarily limit number of state/stack symbols
        limitS = 5
        # arbitrarily limit length of suffix added in any stack operation
        limitL = 2

        # limit search to the observed input alphabet
        inputalph = set()

        if mode == 'simple':

            for l in fileinput.input(files, mode='rb'):

                t.add(l[:-1], True)
                inputalph = inputalph.union(l[:-1])

                print(b"; ".join([w for (w, st, info, has_children) in t.iter()]))
                print("; ".join(['(%s,%s)' % (w, pprint.saferepr(i)) for (w, st, i, has_children) in t.iter()]))
                a = Automaker(t, limitS, limitL)
                a.setupProblem()
                a.set_alphabet(inputalph)
                a.askZ3()

        elif mode == 'advanced':

            a = Automaker(t, limitS, limitL)
            a.setupProblem()

            question = None
            prompt = "dPDA wizard :> "
            
            if len(files) < 1:
                print (prompt, end='', flush=True)
                
            for l in fileinput.input(files, mode='rb'):
                inp = None
                
                # assert a positive example:
                if l[0] == b'p'[0] or l[0] == b'y'[0]:
                    inp = unescape(l[2:-1])
                    if question != None and not inp:
                        inp = question
                        question = None
                    pol = True
                
                # assert a negative example:
                elif l[0] == b'n'[0] or l[0] == b'n'[0]:
                    inp = unescape(l[2:-1])
                    if question != None and not inp:
                        inp = question
                        question = None
                    pol = False
  
                # query
                elif l[0] == b'?'[0]:
                    print ("asking Z3")
                    sat = a.askZ3()
                    
                    # ...
                    # print(a.automaton.D)
                    # print(a.automaton.QF)

                    if sat:
                        checkalph = List(inputalph)
                        print ("here's some words (alphabet %s)" % checkalph)
                        try:
                            en = a.enumerate_words_t(checkalph, b"")
                            for w in itertools.islice(en, 0, 14):
                                print (w)
                        except StopIteration:
                            print ("oops, language is not infinite")
                        except RecursionError:
                            print ("RecursionError (this is a bug)")
                            
                        question = t.first_word_not_in(checkalph)
                        

                # quit
                elif l[0] == b'q'[0]:
                    exit(0)
                    
                elif l[0] == b's'[0]:
                    limitS = int(l[2:])
                    print ("number of internal symbols set to %d" % limitS)
                
                # process input in case of assertion
                if inp != None:
                    suffix = t.add(inp, pol)
                    inputalph = inputalph.union(inp)

                    print ('asserting %s %s' % (pol, inp))

                    a = Automaker(t, limitS, limitL)
                    a.setupProblem()
                    a.set_alphabet(inputalph)
                    
                if len(files) < 1:
                    if question == None:
                        prompt = "dPDA wizard :> "
                    else:
                        prompt = "%s? :>" % repr(question)
                    print (prompt, end='', flush=True)
                
                

    except KeyboardInterrupt as e:
        pass
        raise e

