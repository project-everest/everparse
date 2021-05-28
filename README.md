# EverParse

| Linux | Windows |
|---------|-------|
| [![Linux](https://msr-project-everest.visualstudio.com/Everest/_apis/build/status/QuackyDucky/QuackyDucky-Linux?branchName=master)](https://msr-project-everest.visualstudio.com/Everest/_build/latest?definitionId=36&branchName=master) | [![Windows](https://msr-project-everest.visualstudio.com/Everest/_apis/build/status/QuackyDucky/everparse-windows-minimal-ci?branchName=master)](https://msr-project-everest.visualstudio.com/Everest/_build/latest?definitionId=50&branchName=master) |

EverParse is a framework for generating verified secure parsers from DSL format specification languages.
It consists of LowParse, a verified combinator library (in `src/lowparse`), and QuackyDucky, an untrusted message format specification language compiler.

For more information, you can read:
* The [EverParse project website](https://project-everest.github.io/everparse)
* our [Microsoft Research blog post](https://www.microsoft.com/en-us/research/blog/everparse-hardening-critical-attack-surfaces-with-formally-proven-message-parsers/)
* our [USENIX Security 2019 paper](https://www.microsoft.com/en-us/research/publication/everparse/).

## Dependencies

EverParse depends on [F*](https://github.com/FStarLang/FStar) and [KreMLin](https://github.com/FStarLang/kremlin).
We recommend to setup your environment using the [everest script](https://github.com/project-everest/everest) - it will automate the installation of dependencies (OCaml, opam packages, Z3, Python, F*, etc). Note that setting up an Everest environment from scratch can take time - if you are in a hurry, consider using a containerized build instead.

## Container Images

EverParse is part of [Project Everest](https://project-everest.github.io). Everest CI maintains up-to-date Docker Images on Docker Hub for [Linux](https://hub.docker.com/r/projecteverest/everest-linux). Those Docker images include a fully built and tested EverParse in the `quackyducky` subdirectory.

## Usage

### Example format description files

[Complete TLS 1.3 message format of miTLS](https://github.com/project-everest/mitls-fstar/blob/dev/src/parsers/Parsers.rfc)

[Bitcoin blocks and transactions](https://github.com/project-everest/everparse/blob/master/tests/bitcoin.rfc)

### Building
`make`

### Running
`./bin/qd.exe -help`
