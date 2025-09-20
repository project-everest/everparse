all: quackyducky-unit-test quackyducky-sample-test quackyducky-sample0-test quackyducky-sample-low-test

.PHONY: all

.gen-test.touch: ../bin/qd.exe unittests.rfc bitcoin.rfc
	rm -f unit/*.fst unit/*.fsti
	../bin/qd.exe -odir unit unittests.rfc
	../bin/qd.exe -low -odir unit bitcoin.rfc
	touch $@

quackyducky-unit-test: .gen-test.touch
	+$(MAKE) -C unit

.PHONY: quackyducky-unit-test

quackyducky-sample-test:
	+$(MAKE) -C sample

.PHONY: quackyducky-sample-test

quackyducky-sample-low-test:
	+$(MAKE) -C sample_low

.PHONY: quackyducky-sample-low-test

quackyducky-sample0-test:
	+$(MAKE) -C sample0

.PHONY: quackyducky-sample0-test
