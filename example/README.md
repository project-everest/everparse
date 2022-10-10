# QuackyDucky example

This documentation is a walkthrough of the `quackyducky` executable that generates parser/serialiser pairs.

`quackyducky` is the compiler that generates parsers, serialisers, lemmas and theorems in F* out of a description of a message format. It is described in details in the [USENIX Security 2019 paper](https://www.microsoft.com/en-us/research/publication/everparse/).

## Walkthrough

First you have to write a description of the format you want the parser/serialiser for. The format is very similar to C structs. The available types and examples can be found in the [USENIX Security 2019 paper](https://www.microsoft.com/en-us/research/publication/everparse/).


As an example, here is a description file:

```
struct {
    uint16 id;
    uint32 list<12..42>;
    uint32 list2<32..234>;
} content_one;

struct {
    uint32 size;
    uint64 a[size];
} content_two;

enum {
    one (0x4242), /* Constant tag */
    two (0x4241),
    (65535) /* Indicates 16 bit representation */ 
} content_type; /* Enum with 2 defined cases */ 

struct {
    uint32 id;
    content_type c_t;
    select (c_t){
        case one: content_one;
        case two: content_two;
    } inner_content;
    uint16 arr[412];
} message;
```

Now, run `./build_docker.sh` (`./build_docker.ps1` respectively) to build the docker image.

Once it is done, run `./run_docker.sh` (`./run_docker.ps1` respectively) to start a docker container and open a shell inside.

## Simple example by hand

In the docker container:
- `cd /pwd/files/simple_example` to go to the `./files/simple_example` folder next to this README file.
- run `quackyducky -odir code -low specs.qd` command to generate the F* code files in `code` folder. It will generate `.fst` and `.fsti` files that contain the parsers, serialisers and proofs.
- run `cd code && fstar --z3rlimit 3000 --already_cached +Prims,+FStar,+LowStar,+C,+Spec.Loops,+LowParse  --include $LOWPARSE_HOME --include $KRML_HOME/krmllib --include $KRML_HOME/krmllib/obj --cmi --expose_interfaces *.fst *.fsti ` to verify the F* code. If the verification times out, you can modify the value of the option `--z3rlimit`.

## Example using `make` to generate C code

In the docker container:

- `cd /pwd/files/make_example` to go to the `./files/make_example` folder next to this README file.
- run `make clean`
- fill `specs.qd`
- run `./generate_code.sh -low` or `./generate_code.sh -high`
- run `make`
- C code is output in the `out` folder
