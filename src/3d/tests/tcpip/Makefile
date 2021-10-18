QD_HOME ?= $(realpath ../../../..)
export QD_HOME
EVERPARSE_HOME=$(QD_HOME)
EVERPARSE_CMD=$(QD_HOME)/bin/3d.exe
SOURCE_FILES=ICMP.3d IPV4.3d TCP.3d Ethernet.3d VXLAN.3d UDP.3d IPV6.3d

all: $(SOURCE_FILES)
	$(EVERPARSE_CMD) --batch $^


interpret: $(SOURCE_FILES)
	$(EVERPARSE_CMD) --batch $^ --interpret

.PHONY: all

INCLUDES=$(QD_HOME)/src/3d/prelude $(QD_HOME)/src/3d/prelude/buffer $(QD_HOME)/src/lowparse $(KREMLIN_HOME)/kremlib/obj $(KREMLIN_HOME)/kremlib

FSTAR_OPTIONS=$(addprefix --include , $(INCLUDES))

%.fst-in:
	@echo $(FSTAR_OPTIONS)
