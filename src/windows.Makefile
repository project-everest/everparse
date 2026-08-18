ifeq ($(OS),Windows_NT)
  EVERPARSE_SRC_PATH := $(shell cygpath -m $(EVERPARSE_SRC_PATH))
endif
