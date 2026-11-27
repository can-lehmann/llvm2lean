LEAN_BIN ?= $(HOME)/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin

all: QuickSort/Generated.lean
	$(LEAN_BIN)/lake build

QuickSort/Generated.lean: ../../test/llvm/quick_sort.ll ../../bin/main
	../../bin/main $< -o $@

clean:
	rm -rf .lake
