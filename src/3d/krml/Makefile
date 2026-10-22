all: headers

extract-krml:
	+$(MAKE) -f extract.Makefile extract-krml

# Direct-C headers do not depend on the validators' runtime .krml library.
headers:
	+$(MAKE) -f header.Makefile headers

.PHONY: all extract-krml headers

clean:
	+$(MAKE) -f extract.Makefile clean
	+$(MAKE) -f header.Makefile clean-headers

.PHONY: clean
