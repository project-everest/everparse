# Pick up a user-configured Z3 version from config.Makefile, if any.
# EVERPARSE_SRC_PATH is set by the internal EverParse Makefiles to the
# absolute path of the src/ directory, so that config.Makefile (which lives
# at the repository root, produced by ./configure) can be located here.
# When this file is included directly by deps.Makefile (which runs from the
# repository root and includes config.Makefile itself), EVERPARSE_SRC_PATH is
# not set, so we skip this include.
ifneq (,$(EVERPARSE_SRC_PATH))
-include $(EVERPARSE_SRC_PATH)/../config.Makefile
endif

EVERPARSE_Z3_VERSION ?= 4.13.3
export EVERPARSE_Z3_VERSION
