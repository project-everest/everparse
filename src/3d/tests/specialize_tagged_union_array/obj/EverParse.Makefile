$(EVERPARSE_OUTPUT_DIR)/EverParseEndianness.h : 
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step copy_everparse_h

$(EVERPARSE_OUTPUT_DIR)/EverParse.h : $(EVERPARSE_OUTPUT_DIR)/EverParseEndianness.h

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.o : $(EVERPARSE_OUTPUT_DIR)/EverParse.h $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.c $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.h $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.h
	$(CC) $(CFLAGS) -I $(EVERPARSE_INPUT_DIR) -I $(EVERPARSE_OUTPUT_DIR)  -c -o $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.o $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.c

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.o : $(EVERPARSE_OUTPUT_DIR)/EverParse.h $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.c $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.h
	$(CC) $(CFLAGS) -I $(EVERPARSE_INPUT_DIR) -I $(EVERPARSE_OUTPUT_DIR)  -c -o $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.o $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.c

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti : $(EVERPARSE_INPUT_DIR)/SpecializeTaggedUnionArray.3d
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --no_batch $(EVERPARSE_INPUT_DIR)/SpecializeTaggedUnionArray.3d

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fst : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fsti : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.c : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.h : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti.checked : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step verify $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fsti.checked : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fsti $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti.checked
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step verify $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fst.checked : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fst $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fsti.checked
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step verify $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fst

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray_ExternalAPI.krml : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti.checked
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step extract $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.ExternalAPI.fsti

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.krml : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fst.checked
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__micro_step extract $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.fst

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.c : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.krml $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray_ExternalAPI.krml
	$(EVERPARSE_CMD) --odir $(EVERPARSE_OUTPUT_DIR) --__produce_c_from_existing_krml $(EVERPARSE_INPUT_DIR)/SpecializeTaggedUnionArray.3d

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.h : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.c

$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray_ExternalAPI.h : $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.c

EVERPARSE_ALL_H_FILES=$(EVERPARSE_OUTPUT_DIR)/EverParse.h $(EVERPARSE_OUTPUT_DIR)/EverParseEndianness.h $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.h $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray_ExternalAPI.h $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.h
EVERPARSE_ALL_C_FILES=$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.c $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.c
EVERPARSE_ALL_O_FILES=$(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArrayWrapper.o $(EVERPARSE_OUTPUT_DIR)/SpecializeTaggedUnionArray.o
