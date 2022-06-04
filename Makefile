.PHONY: all

all: FO-prover

FO-prover: $(shell find . -name '*.hs')
	stack build && stack install --local-bin-path ./ && mv prover-exe FO-prover

test: FO-prover
	./run_tests.sh

clean:
	rm -rf FO-prover *.hi *.o ./.stack-work ./points.txt ./score.txt ./out ./.idea *.iml