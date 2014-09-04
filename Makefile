SRC_MODULES := \
	AbstractStencil \
	HoareLogic \
	DistrKernel
SRC_VS := $(SRC_MODULES:%=src/%.v)

.PHONY: src clean

src: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(SRC_VS)
	coq_makefile -R src Stencils $(SRC_VS) -o Makefile.coq


clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
