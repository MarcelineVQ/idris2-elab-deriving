# literally just convenience

PKGNAME = elab-deriving

.PHONY: build

install:
	idris2 --install ${PKGNAME}.ipkg

build:
	idris2 --build ${PKGNAME}.ipkg

test:
	@${MAKE} -C tests only=$(only)

clean:
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;
