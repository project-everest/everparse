all: fine.do coarse.do

%.do:
	+$(MAKE) -C $(basename $@)

# Both subdirectories have their own clean; without this the outer clean stops
# at this directory.
clean: fine.clean coarse.clean

%.clean:
	+$(MAKE) -C $(basename $@) clean

.PHONY: all clean %.do %.clean
