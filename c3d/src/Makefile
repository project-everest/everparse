.PHONY: test

ifeq (${CLANG_BUILD},)
$(error "Please define $$CLANG_BUILD, it should point to your clang build directory")
endif

test:
	make -C out/
	${CLANG_BUILD}/bin/clang -mllvm -debug-only=c3d -std=c2x -fplugin=./out/C3d.so ../tests/basic0.h
	cat ../tests/basic0.3d
