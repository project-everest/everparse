all: test

demo.do:

dpe.do:

unit.do:

rust.do:

test: demo.do dpe.do rust.do unit.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do
