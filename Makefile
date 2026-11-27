LLVM_FLAGS := $(shell llvm-config-22 --cxxflags --ldflags)

bin/main: src/main.cpp
	clang++ $(LLVM_FLAGS) -o $@ $^
