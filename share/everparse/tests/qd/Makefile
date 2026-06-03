all: unit.do

.PHONY: all

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: %.do

clean: unit.clean

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
