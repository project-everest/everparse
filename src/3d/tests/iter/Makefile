all: fine.do coarse.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all %.do
