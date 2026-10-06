include include.Makefile

all: Test.3d
	$(3D) --odir tmp --makefile nmake Test.3d --skip_o_rules
	+$(MAKE) -f test.Makefile

.PHONY: all

clean:
	rm -rf tmp

.PHONY: clean
