LLVM_FLAGS := $(shell llvm-config-22 --cxxflags --ldflags --libs core irreader support)

bin/main: src/main.cpp
	clang++ $(LLVM_FLAGS) -o $@ $^
