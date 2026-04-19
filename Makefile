.PHONY: build safe-build

build:
	lake build

safe-build:
	@echo "=== Step 1: Environment Preparation ==="
	ulimit -s unlimited && lake clean
	@echo "=== Step 2: Sequential Round Compilation (Zeta Reduction Protection) ==="
	@for i in $$(seq 0 23); do \
		echo "Building Round $$i..."; \
		lake build KeccakEngine.Verify.Round$$i || exit 1; \
	done
	@echo "=== Step 3: Final Linking ==="
	lake build
	@echo "=== SUCCESS: Project is fully verified and built! ==="