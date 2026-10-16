MODULES=3d cbor cddl lowparse qd

all: $(addsuffix .do,$(MODULES))

.PHONY: all

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: %.do

clean: $(addsuffix .clean,$(MODULES))

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
