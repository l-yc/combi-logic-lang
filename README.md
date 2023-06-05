# Mini Verified Combinational Logic Language

In-progress MIT UROP (Winter 2023 - Spring 2023)

## build

```sh
coq_makefile -f _CoqProject -o Makefile
make
```

## TODOs

- [ ] replace fmap with [coqutils](https://github.com/mit-plv/coqutil) map
- [ ] phoas for var names 
- [ ] prove lemmas related to `var_names`, `interpret`, and `run`
- [ ] complete barrel shifter proofs
- [ ] add adder proof
