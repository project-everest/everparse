ifeq ($(OS),Windows_NT)
  EVERPARSE_HOME := $(shell cygpath -m $(EVERPARSE_HOME))
endif
