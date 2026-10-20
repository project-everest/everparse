all: extract-krml headers

extract-krml:
	+$(MAKE) -f extract.Makefile extract-krml

# The reference generator still needs .krml; direct-C headers are independent.
RUNTIME_HEADER_GENERATOR ?= karamel
ifeq (karamel,$(RUNTIME_HEADER_GENERATOR))
headers: extract-krml
endif
headers:
	+$(MAKE) -f header.Makefile headers

.PHONY: all extract-krml headers

clean:
	+$(MAKE) -f extract.Makefile clean
	+$(MAKE) -f header.Makefile clean-headers

.PHONY: clean
