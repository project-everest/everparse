# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version
ARG CI_THREADS=24

ADD --chown=opam:opam ./ $HOME/everparse/

# Install F* and Karamel from the Karamel CI install script
# FIXME: the `opam depext` command should be unnecessary with opam 2.1
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
RUN sudo apt-get update && sudo apt-get install --yes --no-install-recommends \
    jq \
    && git clone --branch taramana_no_steel https://github.com/FStarLang/karamel $KRML_HOME && \
    eval $(opam env) && $KRML_HOME/.docker/build/install-deps.sh && \
    env OTHERFLAGS='--admit_smt_queries true' make -C $KRML_HOME -j $CI_THREADS

# Clone and build Steel
ENV STEEL_HOME=$HOME/steel
RUN git clone https://github.com/FStarLang/steel $STEEL_HOME && \
    eval $(opam env) && env OTHERFLAGS='--admit_smt_queries true' make -k -j $CI_THREADS -C $STEEL_HOME

# CI proper
WORKDIR $HOME/everparse
ENV STEEL_C=1
RUN eval $(opam env) && make -j $CI_THREADS steel-unit-test
