QD_HOME ?= $(realpath ../../../..)
export QD_HOME
EVERPARSE_HOME=$(QD_HOME)
EVERPARSE_CMD=$(QD_HOME)/src/3d/3d
SOURCE_FILES=ICMP.3d IPHeader.3d TCP.3d

all: $(SOURCE_FILES)
	$(EVERPARSE_CMD) --batch $^

.PHONY: all
