# This Dockerfile builds and tests c3d
# It should be built from the parent directory

FROM projecteverest/clang-c3d

# Install some c3d build dependencies
RUN apt-get update
RUN apt-get --yes install --no-install-recommends make binutils tar gzip libstdc++-9-dev libc-dev libgcc-9-dev libc-dev sudo

# Install cmake
WORKDIR /root
ADD https://github.com/Kitware/CMake/releases/download/v3.18.1/cmake-3.18.1-Linux-x86_64.tar.gz .
RUN tar xf cmake-3.18.1-Linux-x86_64.tar.gz
RUN mv cmake-3.18.1-Linux-x86_64 /opt/cmake

# Create a new user and give them sudo rights
RUN useradd -d /home/test test
RUN echo 'test ALL=NOPASSWD: ALL' >> /etc/sudoers
RUN mkdir /home/test
RUN chown test:test /home/test
USER test
ENV HOME /home/test
WORKDIR $HOME

# Declare clang-c3d as default C/C++ compilers
ENV LLVM_BUILD_ROOT /opt/clang-c3d
ENV CC $LLVM_BUILD_ROOT/bin/clang
ENV CXX $LLVM_BUILD_ROOT/bin/clang++

# Build and test c3d
COPY src src
COPY tests tests
RUN sudo chown --recursive test:test src tests
RUN mkdir out
WORKDIR out
RUN /opt/cmake/bin/cmake -D LLVM_BUILD_ROOT=$LLVM_BUILD_ROOT ../src/ && make -j
RUN $LLVM_BUILD_ROOT/bin/clang  -fplugin=./C3d.so -std=c2x -mllvm -debug-only=c3d  ../tests/basic0.h

