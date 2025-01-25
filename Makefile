.PHONY: ci
ci:
	cargo test
	cargo run --example parsing
	cargo fix
	cargo fmt
	./tools/check_repository_unchanged.sh

