ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version
RUN sudo apt-get install --no-install-recommends --yes wget

ADD --chown=opam:opam ./ $HOME/asn1star/
WORKDIR $HOME/asn1star

SHELL ["/bin/bash", "--login", "-c"]

# Dependencies (F*, Karamel, EverParse, and their opam package dependencies)
ARG CI_THREADS=24
RUN env OPAMYES=1 CI_THREADS=$CI_THREADS NO_INTERACTIVE=1 ./install-everparse.sh

# TODO: Add F* and krml to path instead
ENV FSTAR_EXE=$HOME/asn1star/everest/FStar/bin/fstar.exe
ENV KRML_HOME=$HOME/asn1star/everest/karamel
ENV EVERPARSE_HOME=$HOME/asn1star/everest/everparse

ENTRYPOINT ["/bin/bash", "--login"]
