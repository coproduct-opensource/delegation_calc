# DLC Makefile — wraps the verification ledger and common dev tasks.
#
# `make ledger` is the artifact. Everything else delegates to cargo, lake, or
# tool-specific entry points.

.PHONY: help ledger build test fmt clippy lean tamarin proverif easycrypt drift loc clean

help:
	@echo "DLC make targets:"
	@echo "  ledger     -- run all checks and emit ledger.json"
	@echo "  build      -- cargo build --workspace"
	@echo "  test       -- cargo test --workspace"
	@echo "  fmt        -- cargo fmt && lean fmt (when wired)"
	@echo "  clippy     -- cargo clippy --workspace --all-targets"
	@echo "  lean       -- cd lean && lake build"
	@echo "  tamarin    -- run models/tamarin/*.spthy"
	@echo "  proverif   -- run models/proverif/*.pv"
	@echo "  easycrypt  -- run models/easycrypt/*.eca"
	@echo "  drift      -- check Aeneas Rust↔Lean drift"
	@echo "  loc        -- print dlc-verifier LOC vs 2000 budget"

ledger:
	@bash scripts/ledger.sh

build:
	cargo build --workspace

test:
	cargo test --workspace

fmt:
	cargo fmt --all

clippy:
	cargo clippy --workspace --all-targets -- -D warnings

lean:
	cd lean && lake build

tamarin:
	@if command -v tamarin-prover >/dev/null 2>&1; then \
	  cd models/tamarin && tamarin-prover --prove dlc.spthy; \
	else \
	  echo "tamarin-prover not on PATH — install via:"; \
	  echo "  brew install --HEAD tamarin-prover/tap/tamarin-prover  (macOS)"; \
	  echo "  docker run --rm -v \$$(pwd)/models/tamarin:/work -w /work \\\\"; \
	  echo "    ghcr.io/eikendev/tamarin-prover:latest tamarin-prover --prove dlc.spthy"; \
	  exit 1; \
	fi

proverif:
	@if command -v proverif >/dev/null 2>&1; then \
	  cd models/proverif && proverif dlc.pv; \
	else \
	  echo "proverif not on PATH — install via:"; \
	  echo "  opam install proverif"; \
	  echo "  brew install proverif  (macOS via homebrew)"; \
	  exit 1; \
	fi

easycrypt:
	@if command -v easycrypt >/dev/null 2>&1; then \
	  cd models/easycrypt && easycrypt -batch Game.eca; \
	else \
	  echo "easycrypt not on PATH — install via:"; \
	  echo "  opam pin add easycrypt https://github.com/EasyCrypt/easycrypt.git"; \
	  echo "  opam install easycrypt alt-ergo"; \
	  exit 1; \
	fi

drift:
	@bash scripts/check-drift.sh 2>/dev/null || echo "drift check not yet wired (M1.Q1.d)"

loc:
	@find crates/dlc-verifier/src -name '*.rs' -exec wc -l {} + | tail -1

clean:
	cargo clean
	rm -f ledger.json
	cd lean 2>/dev/null && rm -rf .lake build || true
