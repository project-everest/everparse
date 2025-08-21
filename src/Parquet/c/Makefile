# ---- USER SETTINGS --------------------------------------------------------
THRIFT_PREFIX ?= $(HOME)/.local/bin/thrift-0.22.0

THRIFT_CGLIB_SRC := $(THRIFT_PREFIX)/lib/c_glib/src

# Built library is usually here after building Thrift:
#   .../lib/c_glib/.libs/libthrift_c_glib.{so,a}
THRIFT_CGLIB_LIBDIR ?= $(THRIFT_PREFIX)/lib/c_glib/.libs

THRIFT_CGLIB_LIBNAME ?= thrift_c_glib

PKG_CFLAGS := $(shell pkg-config --cflags glib-2.0 gobject-2.0 2>/dev/null)
PKG_LIBS   := $(shell pkg-config --libs   glib-2.0 gobject-2.0 2>/dev/null)

CFLAGS += $(PKG_CFLAGS) \
          -I$(THRIFT_CGLIB_SRC)        # so <thrift/c_glib/...> resolves

# LDFLAGS += -L$(THRIFT_CGLIB_LIBDIR)
# LDLIBS  += -l$(THRIFT_CGLIB_LIBNAME) $(PKG_LIBS) -pthread
LDLIBS += $(THRIFT_CGLIB_LIBDIR)/libthrift_c_glib.a $(PKG_LIBS)

# ---- Generated sources/headers from thrift --gen c_glib ----------------
GEN_SRCS = parquet_types.c
GEN_HDRS = parquet_types.h

all: parquet_meta

parquet_meta: main.o $(GEN_SRCS) $(GEN_HDRS)
	$(CC) -o $@ main.o $(GEN_SRCS) $(CFLAGS) $(LDFLAGS) $(LDLIBS)

main.o: main.c $(GEN_HDRS)
	$(CC) -c main.c $(CFLAGS) -o $@

clean:
	rm -f parquet_meta main.o
