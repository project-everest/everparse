all: cose

submodules:
	+$(MAKE) -C opt submodules

export KRML_HOME ?= $(realpath opt/karamel)

cbor: submodules
	+$(MAKE) -C src/cbor/pulse/det

cose: cbor
	+$(MAKE) -C src/cose
