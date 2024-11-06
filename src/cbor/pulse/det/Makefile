all: c.do rust

c.do: krml.do

rust: krml.do
	cd $@ && cargo build

%.do:
	+$(MAKE) -C $(basename $@)

.PHONY: %.do rust
