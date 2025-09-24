all: quackyducky-unit-test quackyducky-sample-test quackyducky-sample0-test quackyducky-sample-low-test

.PHONY: all

unit/Makefile: ../bin/qd.exe unittests.rfc bitcoin.rfc
	mkdir -p $(dir $@)
	rm -f unit/*.fst unit/*.fsti
	../bin/qd.exe -odir unit unittests.rfc
	../bin/qd.exe -low -odir unit bitcoin.rfc
	rm -f $@
	cp unit.Makefile $@
	touch $@

quackyducky-unit-test: unit/Makefile
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

clean: clean-unit sample0.clean sample_low.clean sample.clean bitfields.clean lowparse.clean

.PHONY: clean

clean-unit:
	rm -rf unit

.PHONY: clean-unit

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
