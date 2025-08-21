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
SRCS_C   := Parquet_Pulse_Toplevel.c
SRCS_CPP := parquet_types.cpp shim_parquet_pulse.cpp main.cpp

OBJS_C    := $(SRCS_C:.c=.o)
OBJS_CPP  := $(SRCS_CPP:.cpp=.o)
OBJS      := $(OBJS_C) $(OBJS_CPP)

# ---- flags ----
CPPFLAGS := -I. \
            -I$(KRML_INC) -I$(KRML_MIN)

CFLAGS   := -O2 -Wall -Wextra -Wpedantic -fvisibility=hidden
CXXFLAGS := -O2 -std=c++17 -Wall -Wextra -Wpedantic -fvisibility=hidden

LDLIBS   := -lthrift

# Some platforms need pthread explicitly with Thrift:
LDLIBS   += -pthread

# ---- rules ----
.PHONY: all clean

all: $(BIN)

$(BIN): $(OBJS)
	$(CXX) $(LDFLAGS) -o $@ $^ $(LDLIBS)

# Compile C (KaRaMeL)
%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c -o $@ $<

# Compile C++ (Thrift + shim + main)
%.o: %.cpp
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c -o $@ $<

clean:
	$(RM) $(OBJS) $(BIN)
