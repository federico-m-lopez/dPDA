# dPDA

Automaton inference from examples using z3py
`-m simple`: Positive examples only
`-m advanced`: Both positive and negative examples accepted. Much more useful.

In `-m advanced`, examples can be provided and the solver can be queried in an interactive session:

`p blah`: "blah is a word of L"
`n quux`: "quux is not a word of L"
`?`: automaton?
`q`: quit

(note that examples can be overridden, and `p a` ... `n a` does not lead to `unsat` but rather to an automaton that doesn't accept a).

## Future work

Sample words from automaton

## Related work

[z3gi][1]

[1]: https://gitlab.science.ru.nl/rick/z3gi
