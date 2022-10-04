# EverParse

| Linux | Windows |
|---------|-------|
| [![Linux](https://msr-project-everest.visualstudio.com/Everest/_apis/build/status/QuackyDucky/QuackyDucky-Linux?branchName=master)](https://msr-project-everest.visualstudio.com/Everest/_build/latest?definitionId=36&branchName=master) | [![Windows](https://msr-project-everest.visualstudio.com/Everest/_apis/build/status/QuackyDucky/everparse-windows-minimal-ci?branchName=master)](https://msr-project-everest.visualstudio.com/Everest/_build/latest?definitionId=50&branchName=master) |

EverParse is a framework for generating verified secure parsers from DSL format specification languages.
It consists of LowParse, a verified combinator library (in `src/lowparse`), and QuackyDucky, an untrusted message format specification language compiler.

For more information, you can read:
* The [EverParse project website and user manual](https://project-everest.github.io/everparse), also available in the `doc` subdirectory of this repository as `*.rst` reStructuredText files.
* our [Microsoft Research blog post](https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/)
* our [PLDI 2022 paper](https://www.microsoft.com/en-us/research/publication/hardening-attack-surfaces-with-formally-proven-binary-format-parsers/)
* our [USENIX Security 2019 paper](https://www.microsoft.com/en-us/research/publication/everparse/).

## Download

We publish binary packages for EverParse as GitHub releases: https://github.com/project-everest/everparse/releases

## Build from source

Full build instructions, including how to install dependencies, are available at https://project-everest.github.io/everparse/build.html, or equivalently in `doc/build.rst` in this repository.

## Container Images

Instead of downloading or building EverParse, if you are in a hurry, consider using a containerized build instead, via a Docker image for Everest.

Indeed, EverParse is part of [Project Everest](https://project-everest.github.io). Everest CI maintains up-to-date Docker Images on Docker Hub for [Linux](https://hub.docker.com/r/projecteverest/everest-linux). Those Docker images include a fully built and tested EverParse in the `quackyducky` subdirectory.

## Using QuackyDucky

### Example format description files

[Complete TLS 1.3 message format of miTLS](https://github.com/project-everest/mitls-fstar/blob/dev/src/parsers/Parsers.rfc)

[Bitcoin blocks and transactions](https://github.com/project-everest/everparse/blob/master/tests/bitcoin.rfc)

### Building
`make`

### Running

Everparse offers two different executables:

* `./bin/qd.exe` (or `quackyducky` when using the Docker file in `./example`): this executable produces parser/serializer pairs in F* given an input description similar to C types.

    An example of use of `quackyducky` is detailed in [this documentation]("../example/README.md").
* `./bin/3d.exe` or (`3d`when using the Docker file in `./example`): this executable produces validators in F* given a description in 3d description language.

    The documentation for this executable can be found [here](https://project-everest.github.io/everparse/3d.html).
