INTERACTIVE ?= --interactive

IDRIS2 = idris2

.PHONY: testbin test

all: testbin test

testbin:
	$(IDRIS2) --build tests.ipkg

test:
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --only $(only)

clean:
	$(RM) -r build
	@find . -type f -name 'output' -exec rm -rf {} \;
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
