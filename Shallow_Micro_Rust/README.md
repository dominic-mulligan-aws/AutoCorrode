# A shallow embedding of µRust

This directory contains material related to the shallow embedding of µRust (or
"Micro Rust") in Isabelle/HOL.

To perform a batch build:

```shell
λ> $ISABELLE_HOME/bin/isabelle build -d ../Micro_Rust_Parsing_Frontend -D .
```

To open this session for interactive editing (from within the directory):

```shell
λ> $ISABELLE_HOME/bin/isabelle jedit -d ../Micro_Rust_Parsing_Frontend *.thy &
```
