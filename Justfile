# Just a task runner
# <https://github.com/casey/just>

# shows this help message
help:
    @just -l

# runs the C++ test
cpp:
    cd cpp && touch test/*.cpp && oj-verify run test/dynamic_tree_subtree_add_subtree_sum.test.cpp

# runs the Haskell test
hs:
    cd hs && touch app/* && oj-verify run app/lct-test.hs

# builds the Haskell project
build:
    cd hs && cabal build

[private]
alias b := build
