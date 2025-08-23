tinycbor-build/libtinycbor.a: tinycbor-build
	$(MAKE) -C tinycbor-build

tinycbor:
	rm -rf $@.tmp
	git clone "https://github.com/intel/tinycbor" $@.tmp
	cd $@.tmp && git checkout 45e4641059709862b4e46f3608d140337566334b
	mv $@.tmp $@

tinycbor-build: tinycbor
	cmake -S tinycbor -B tinycbor-build
