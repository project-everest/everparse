ifeq (,$(KRML_EXE))
  $(error please define KRML_EXE to point to the KaRaMeL executable)
endif

KRML_INC  := $(shell $(KRML_EXE) -locate-include)
KRML_MIN  := $(shell $(KRML_EXE) -locate-krmllib)/dist/minimal

# ---- toolchain ----
CC      := gcc
CXX     := g++
AR      := ar
RM      := rm -f

# ---- targets ----
BIN     := parquet_checker

# ---- sources ----
SRCS_C   := EverParquet.c
SRCS_CPP := parquet_types.cpp shim_parquet_pulse.cpp main.cpp

OBJS_C    := $(SRCS_C:.c=.o)
OBJS_CPP  := $(SRCS_CPP:.cpp=.o)
OBJS      := $(OBJS_C) $(OBJS_CPP)

# ---- flags ----
THRIFT_PREFIX ?= $(CURDIR)/thrift-build
THRIFT_HDR    := $(THRIFT_PREFIX)/include/thrift/Thrift.h

CPPFLAGS += -I. \
            -I$(THRIFT_PREFIX)/include \
            -I$(KRML_INC) -I$(KRML_MIN)

CFLAGS   += -O2 -Wall -Wextra -Wpedantic -fvisibility=hidden
CXXFLAGS += -O2 -std=c++17 -Wall -Wextra -Wpedantic -fvisibility=hidden

LDLIBS   += $(THRIFT_PREFIX)/lib/libthrift.a -L$(THRIFT_PREFIX)/lib

# Some platforms need pthread explicitly with Thrift:
LDLIBS   += -pthread

# ---- rules ----
.PHONY: all clean

all: $(BIN)

# Thrift's C++ library needs the Boost headers (>= 1.56). If Boost lives in a
# non-standard prefix, set BOOST_ROOT to point to it.
THRIFT_CONFIGURE_FLAGS := \
  --disable-dependency-tracking --disable-tests --disable-tutorial \
  --with-cpp $(if $(BOOST_ROOT),--with-boost=$(BOOST_ROOT),) \
  --without-c_glib --without-qt5 --without-java --without-kotlin \
  --without-python --without-py3 --without-perl --without-php \
  --without-php_extension --without-ruby --without-go --without-rs \
  --without-nodejs --without-nodets --without-netstd --without-dart \
  --without-erlang --without-lua --without-swift --without-cl \
  --without-haxe --without-d

# Thrift's configure silently downgrades --with-cpp to "no" when it cannot find
# the Boost headers, and then quietly installs nothing under include/thrift, so
# check the outcome before spending time on a build that cannot work.
THRIFT_CHECK_CPP := \
  grep -q '^S\["WITH_CPP_TRUE"\]=""$$' config.status || \
  { echo 'ERROR: Thrift configure disabled the C++ library; install the Boost headers (>= 1.56, e.g. libboost-dev or boost-devel) or set BOOST_ROOT' >&2; exit 1; }

# Depend on an installed header rather than on $(THRIFT_PREFIX): configure
# creates that directory even when it installs nothing into it, so it would be
# considered up to date after a failed build, and its timestamp would keep
# changing and force needless recompilations.
# We only need to rebuild the header for the default THRIFT_PREFIX value,
# because if the user overrode it, we should assume the header already present.
$(CURDIR)/thrift-build/include/thrift/Thrift.h:
	+cd thrift && ./bootstrap.sh && ./configure --prefix=$(THRIFT_PREFIX) $(THRIFT_CONFIGURE_FLAGS) && { $(THRIFT_CHECK_CPP) ; } && $(MAKE) && $(MAKE) install
	test -f $@

$(BIN): $(OBJS) $(THRIFT_HDR)
	$(CXX) $(LDFLAGS) -o $@ $(OBJS) $(LDLIBS)

# Compile C (KaRaMeL)
%.o: %.c $(THRIFT_HDR)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c -o $@ $<

# Compile C++ (Thrift + shim + main)
%.o: %.cpp $(THRIFT_HDR)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c -o $@ $<

clean:
	$(RM) $(OBJS) $(BIN)
