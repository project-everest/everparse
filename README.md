## QuackyDucky

QuackyDucky is a small tool to translate informal specification of message formats found in RFC (in particular for TLS 1.3)
into formal F* specifications, which are in turn transformed into efficient and verified parser implementations.

### Usage

#### Requirements
QuackyDucky requires a modern `ocaml` compiler and build environment. We strongly recommend installing all of your OCaml ecosystem exclusvely via the latest version of `opam`: all other approaches to get OCaml to work reliably and fully are a waste of time. If you can't get `opam` to work, don't bother trying any other method and just forget about this project.

The following OCaml packages are required and can be installed via this `opam` command: `opam install batteries menhir ulex ocamlfind hex ocamlbuild asn1-combinators`.

In case you obtain errors loading your OCaml environment, please make sure the environment is set properly by running `` eval `opam config env` ``.

#### Building
`make`

#### Running
`./bin/quackyducky -help`
