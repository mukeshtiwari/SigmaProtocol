#!/bin/bash
# Follow-on job: starts when the timing queue ends.  Builds only.
S=${WORK:?set WORK to the build directory}
while kill -0 40094 2>/dev/null; do /bin/sleep 20; done
ulimit -s 65520
step() { n=$1; shift; echo "### $n start $(date +%T)"; "$@" > $S/exp/log-$n.txt 2>&1; echo "### $n exit $? $(date +%T)"; }
cake() { mkdir -p $S/exp/cake && tar -xzf $S/cakeml/cake-arm8-64.tar.gz -C $S/exp/cake --strip-components=1 && make -C $S/exp/cake cake; }
s91() { cd $S/exp/sig91 && opam exec --switch=peregrine -- dune build -j 8 _build/default/src/Examples/WasmBenchDefs.vo _build/default/src/Examples/WasmBenchSmallDefs.vo; }
sw() { opam switch create sigma92 ocaml-base-compiler.4.14.2 --no-switch -y &&
  opam repo add --switch=sigma92 rocq-released https://rocq-prover.org/opam/released &&
  opam install --switch=sigma92 -y -j 8 rocq-core.9.2.0 rocq-prover dune rocq-bignums rocq-coqprime rocq-metarocq-erasure-plugin.1.5.1+9.2 rocq-ceres-bytestring.1.0.0; }
te() { rm -rf $S/exp/typed && git clone -q -b rocq-9.2-rust-fixes https://github.com/peregrine-project/rocq-typed-extraction $S/exp/typed && git -C $S/exp/typed checkout -q 5f3c64b && ls $S/exp/typed && opam pin --switch=sigma92 -n -y $S/exp/typed && opam pin --switch=sigma92 list && opam install --switch=sigma92 -y rocq-typed-extraction-common rocq-rust-extraction rocq-elm-extraction; }
fe() { cd $S/exp/sig92 && PATH=$S/exp/shim:$PATH opam exec --switch=sigma92 -- bash bench/peregrine/deps.sh $S/exp/deps > $S/exp/deps.env; }
s92() { cd $S/exp/sig92 && opam exec --switch=sigma92 -- dune build -j 8 _build/default/src/Examples/WasmBenchSmallDefs.vo _build/default/src/Examples/Ed25519Ins.vo; }
step cake cake; step sig91 s91; step switch92 sw; step typed te; step frontend fe; step sig92 s92
echo "### prep done $(date +%T)"
