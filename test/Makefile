TARGETS := $(patsubst source/%.c,llvm/%.ll,$(wildcard source/*.c))

all: $(TARGETS)

llvm/%.ll: source/%.c
	clang -O1 -Xclang -disable-llvm-passes -S -emit-llvm $< -o $@
	opt -S $@ -o $@ --passes=mem2reg

clean:
	-rm -r llvm
	mkdir -p llvm

