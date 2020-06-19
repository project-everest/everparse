# Test CI based on GitHub Actions
# Can also be used standalone

FROM projecteverest/kremlin-linux:3659197bb45c
ENV FSTAR_HOME $HOME/FStar
ENV KREMLIN_HOME $HOME/kremlin

# # Install the dependencies of Project Everest
# RUN apt-get update
# RUN apt-get --yes --no-install-recommends install software-properties-common dirmngr gpg-agent
# RUN apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv-keys 3FA7E0328081BFF6A14DA29AA6A19B38D3D831EF
# RUN apt-get update
# RUN apt-get --yes install --no-install-recommends opam emacs-nox gcc binutils make m4 git time gnupg ca-certificates sudo

SHELL ["/bin/bash", "--login", "-c"]

# Install OCaml
ENV OPAMYES 1
# RUN opam init --disable-sandboxing --compiler=4.09.1
RUN opam env --set-switch | tee --append .profile .bashrc .bash_profile

# # Install emacs F* mode
# ADD --chown=everest src/package/fstar.sh bin/fstar.sh
# ADD --chown=everest src/package/init.el .emacs.d/init.el
# ADD --chown=everest src/package/install-fstar-mode.el .emacs.d/install-fstar-mode.el
# RUN emacs --script .emacs.d/install-fstar-mode.el

# Add the project files proper
RUN mkdir $HOME/everparse
WORKDIR $HOME/everparse
ADD --chown=everest src/lowparse/* src/lowparse/
ADD --chown=everest tests/layeff/* tests/layeff/
ADD --chown=everest Makefile Makefile

# Clone and build Project Everest
ARG EVEREST_THREADS=1
RUN tests/layeff/install-everest.sh
RUN cat everest-env.sh | tee --append $HOME/.profile $HOME/.bashrc $HOME/.bash_profile

# Test
ENV QD_HOME $HOME/everparse
RUN make -j $EVEREST_THREADS -k lowparse
RUN make -j $EVEREST_THREADS -k -C tests/layeff

ENTRYPOINT ["/bin/bash", "--login"]
