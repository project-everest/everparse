all: pulse/det-c.do

test: pulse/det-c/test.do

spec.do:

spec/raw.do: spec.do

spec/raw/everparse.do: spec/raw.do

pulse.do: spec.do

pulse/raw.do: spec/raw.do pulse.do

pulse/raw/everparse.do: pulse/raw.do spec/raw/everparse.do

pulse/det-c.do: pulse/raw/everparse.do

pulse/det-c/test.do: pulse/det-c.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do
