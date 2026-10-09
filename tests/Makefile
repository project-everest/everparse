# The Low* suites that used to live here (unit, sample, sample0, sample_low,
# bitfields, lowparse) were removed along with the Low* backend; their Pulse
# counterparts are in share/everparse/tests/qd and share/everparse/tests/lowparse.
# Only tests/pulse remains, and it is not yet wired into lowparse-pulse-test.

clean: pulse.clean

.PHONY: clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: %.clean
