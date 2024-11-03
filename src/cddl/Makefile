all: pulse.do

pulse.do: spec.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all %.do
