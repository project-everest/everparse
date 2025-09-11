all: tool.do

pulse.do: spec.do

tool.do: pulse.do

demo.do: tool.do

tests.do: tool.do

test: tests.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do
