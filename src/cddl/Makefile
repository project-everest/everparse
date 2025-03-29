all: tool.do

pulse.do: spec.do

tool.do: pulse.do

demo.do: tool.do

test.do: tool.do

test: test.do demo.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do
