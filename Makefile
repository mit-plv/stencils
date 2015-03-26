SOURCES_MODULES := \
	Sets \
	SetsFacts \
	Expressions \
	Problems \
	Programs \
	Kernels \
	Automation \
	Domains \
	Main
SOURCES_VS  := $(SOURCES_MODULES:%=sources/%.v)
SOURCES_VOS := $(SOURCES_MODULES:%=sources/%.vo)

EXAMPLES_MODULES := \
	HeatEquation2D \
	AmericanPutStockOptionPricing \
	PairwiseSequenceAlignment \
	CacheOblivious1D \
	Utils \
	ThreePointNaive \
	ThreePoint
EXAMPLES_VS  := $(EXAMPLES_MODULES:%=examples/%.v)
EXAMPLES_VOS := $(EXAMPLES_MODULES:%=examples/%.vo)

.PHONY: sources examples cleanup

sources: Makefile.coq $(SOURCES_VOS)

examples: Makefile.coq $(EXAMPLES_VOS)

Makefile.coq: Makefile $(SOURCES_VS) $(EXAMPLES_VS)
	coq_makefile -R sources StLib -R examples StExamples $(SOURCES_VS) $(EXAMPLES_VS) -o Makefile.coq

-include Makefile.coq

cleanup: clean
	rm -rf Makefile.coq
	rm -rf nlia.cache
	rm -rf examples/lia.cache
	rm -rf examples/nlia.cache
