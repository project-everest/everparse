all: tool.do

pulse.do: spec.do

tool.do: pulse.do

demo.do: tool.do

test.do: tool.do

unit-tests.do: tool.do

test-rust.do: tool.do

test: test.do demo.do unit-tests.do test-rust.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do
