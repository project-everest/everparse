all: c.do rust.do

c.do: krml.do

rust.do: krml.do

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: %.do
