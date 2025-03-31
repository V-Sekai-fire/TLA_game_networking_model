default: demo

# brew install ghc cabal-install haskell-stack haskell-platform llvm

clone:
	git clone https://github.com/bugarela/tla-transmutation.git

build:
	cd tla-transmutation && stack build

demo: build
	cd tla-transmutation && ./target/release/tla-transmutation --help

test:
	cd tla-transmutation && stack test

clean:
	cd tla-transmutation && stack clean
