all: tool.do

pulse.do: spec.do

tool.do: pulse.do

demo.do: tool.do

tests.do: tool.do

test: tests.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do

clean: spec.clean pulse.clean tool.clean tests.clean

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
