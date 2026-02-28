$(EVERPARSE_OUTPUT_DIR)/EverParseEndianness.h : 
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step copy_everparse_h

$(EVERPARSE_OUTPUT_DIR)/EverParse.h : $(EVERPARSE_OUTPUT_DIR)/EverParseEndianness.h

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.o : $(EVERPARSE_OUTPUT_DIR)/EverParse.h $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.c $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.h $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.h
	$(CC) $(CFLAGS) -I $(EVERPARSE_INPUT_DIR) -I $(EVERPARSE_OUTPUT_DIR)  -c -o $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.o $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.c

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.o : $(EVERPARSE_OUTPUT_DIR)/EverParse.h $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.c $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.h
	$(CC) $(CFLAGS) -I $(EVERPARSE_INPUT_DIR) -I $(EVERPARSE_OUTPUT_DIR)  -c -o $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.o $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.c

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti : $(EVERPARSE_INPUT_DIR)/SpecializeVLArray.3d
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --no_batch $(EVERPARSE_INPUT_DIR)/SpecializeVLArray.3d

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fst : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fsti : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.c : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.h : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti.checked : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step verify $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fsti.checked : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fsti $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti.checked
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step verify $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fst.checked : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fst $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fsti.checked
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step verify $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fst

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray_ExternalAPI.krml : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti.checked
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step extract $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.krml : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fst.checked
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step extract $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.fst

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.c : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.krml $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray_ExternalAPI.krml
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__produce_c_from_existing_krml $(EVERPARSE_INPUT_DIR)/SpecializeVLArray.3d

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.h : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.c

$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray_ExternalAPI.h : $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.c

EVERPARSE_ALL_H_FILES=$(EVERPARSE_OUTPUT_DIR)/EverParse.h $(EVERPARSE_OUTPUT_DIR)/EverParseEndianness.h $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.h $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray_ExternalAPI.h $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.h
EVERPARSE_ALL_C_FILES=$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.c $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.c
EVERPARSE_ALL_O_FILES=$(EVERPARSE_OUTPUT_DIR)/SpecializeVLArrayWrapper.o $(EVERPARSE_OUTPUT_DIR)/SpecializeVLArray.o
