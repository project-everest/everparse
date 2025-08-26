ifeq (,$(KRML_HOME))
  $(error please define KRML_HOME to point to the root of your KaRaMeL git checkout)
endif

KRML_INC  := $(KRML_HOME)/include
KRML_MIN  := $(KRML_HOME)/krmllib/dist/minimal

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

CPPFLAGS += -I. \
            -I$(THRIFT_PREFIX)/include \
            -I$(KRML_INC) -I$(KRML_MIN)

CFLAGS   += -O2 -Wall -Wextra -Wpedantic -fvisibility=hidden
CXXFLAGS += -O2 -std=c++17 -Wall -Wextra -Wpedantic -fvisibility=hidden

LDLIBS   += -lthrift -L$(THRIFT_PREFIX)/lib

# Some platforms need pthread explicitly with Thrift:
LDLIBS   += -pthread

# ---- rules ----
.PHONY: all clean

all: $(BIN)

$(CURDIR)/thrift-build:
	+cd thrift && ./bootstrap.sh && ./configure --prefix=$@ --with-cpp --without-perl --without-python --disable-dependency-tracking && $(MAKE) && $(MAKE) install

$(BIN): $(OBJS) $(THRIFT_PREFIX)
	$(CXX) $(LDFLAGS) -o $@ $(OBJS) $(LDLIBS)

# Compile C (KaRaMeL)
%.o: %.c $(THRIFT_PREFIX)
	$(CC) $(CPPFLAGS) $(CFLAGS) -c -o $@ $<

# Compile C++ (Thrift + shim + main)
%.o: %.cpp $(THRIFT_PREFIX)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c -o $@ $<

clean:
	$(RM) $(OBJS) $(BIN)
