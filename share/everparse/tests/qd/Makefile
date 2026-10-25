MODULES=unit

all: $(addsuffix .do,$(MODULES))

.PHONY: all

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: %.do

clean: $(addsuffix .clean,$(MODULES))

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
