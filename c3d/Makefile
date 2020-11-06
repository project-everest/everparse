.PHONY: test

TESTFILE=tests/basic0.h

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

OURCLANG=${CLANG_BUILD}/bin/clang

# This is the compiler that will be used to compile the plugin
# itself. It doesn't have to be clang: you can use gcc too, other
# compilers *may* work too, but we support only clang. You *could*
# also point this to ${OURCLANG}, but might be terribly slow if
# you compiled OURCLANG with debugging enabled. On changing this
# you should delete out/.
CC = clang

test: out
	make -C out/
	${OURCLANG} -mllvm -debug-only=c3d -std=c2x -fblocks -fplugin=./out/src/C3d.so -include ../tests/prelude.h ${TESTFILE}
	cat $(patsubst %.h,%.3d,${TESTFILE})

out:
	mkdir -p out
	cd out/ && cmake -D LLVM_BUILD_ROOT=${CLANG_BUILD}	\
		../
