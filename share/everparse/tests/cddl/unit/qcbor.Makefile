QCBOR/libqcbor.a: QCBOR
	# Override the CFLAGS to use -O3, for a more fair comparison
	$(MAKE) -C QCBOR CFLAGS="-I inc -I test -O3 -fPIC"
