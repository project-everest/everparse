all: extract-krml headers

extract-krml:
	+$(MAKE) -f extract.Makefile extract-krml

# The per-backend EverParse.h shipped alongside the .krml files. Depends on
# extract-krml, which produces the .krml files it is generated from.
headers: extract-krml
	+$(MAKE) -f header.Makefile headers

.PHONY: all extract-krml headers

clean:
	+$(MAKE) -f extract.Makefile clean
	+$(MAKE) -f header.Makefile clean-headers

.PHONY: clean
