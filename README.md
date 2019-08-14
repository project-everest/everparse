# EverParse

EverParse is a framework for generating verified secure parsers from DSL format specification languages.
It consists of LowParse, a verified combinator library (in `src/lowparse`), and QuackyDucky, an untrusted message format specification language compiler.

For more information, you can read our [USENIX Security 2019 paper](https://www.microsoft.com/en-us/research/publication/everparse/).

## Dependencies

EverParse depends on [F*](https://github.com/FStarLang/FStar) and [KreMLin](https://github.com/FStarLang/kremlin).
We recommend to setup your environment using the [everest script](https://github.com/project-everest/everest) - it will automate the installation of dependencies (OCaml, opam packages, Z3, Python, F*, etc). Note that setting up an Everest environment from scratch can take time - if you are in a hurry, consider using a containerized build instead.

## Container Images

Our CI maintains up to date Docker images on DockerHub for [Linux](https://hub.docker.com/r/projecteverest/quackyducky-linux) and [Windows](https://hub.docker.com/r/projecteverest/quackyducky-windows-nt)

## Usage

### Example format description files

[Complete TLS 1.3 message format of miTLS](https://github.com/project-everest/mitls-fstar/blob/dev/src/parsers/Parsers.rfc)
[Bitcoin blocks and transactions](https://github.com/project-everest/everparse/blob/master/tests/bitcoin.rfc)

### Building
`make`

### Running
`./bin/quackyducky -help`
