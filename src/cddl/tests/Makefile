all: test

demo.do:

dpe.do:

unit.do:

rust.do:

others: demo.do rust.do

.PHONY: others

test: others dpe.do unit.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: all test %.do
