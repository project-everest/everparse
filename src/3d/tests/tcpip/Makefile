QD_HOME ?= $(realpath ../../../..)
export QD_HOME
EVERPARSE_HOME=$(QD_HOME)
EVERPARSE_CMD=$(QD_HOME)/bin/3d.exe
SOURCE_FILES=ICMP.3d IPV4.3d TCP.3d Ethernet.3d VXLAN.3d UDP.3d IPV6.3d

all: $(SOURCE_FILES)
	$(EVERPARSE_CMD) --batch $^

.PHONY: all
