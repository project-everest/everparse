.PHONY: test

TESTFILE=../tests/basic0.h

ifeq (${CLANG_BUILD},)
$(error "Please define $$CLANG_BUILD, it should point to your clang build directory")
endif

ifeq ($(OS),Windows_NT)
	SO = dll
else
ifeq ($(uname -s),Darwin)
	SO = dylib
else
	SO = so
endif
endif

test: out
	make -C out/
	${CLANG_BUILD}/bin/clang -mllvm -debug-only=c3d -std=c2x -fplugin=./out/C3d.so ${TESTFILE}
	cat $(patsubst %.h,%.3d,${TESTFILE})

out:
	mkdir -p out
	cd out/ && cmake -D LLVM_BUILD_ROOT=${CLANG_BUILD} ../
