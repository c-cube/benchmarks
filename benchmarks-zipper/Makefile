
all:
	cd ../benchmarks/ && \
	  find -name '*.smt2' | while read i ; do \
	    mkdir -p ../benchmarks-zipper/`dirname $$i` ; \
	    tip $$i --type-skolem-conjecture --int-to-nat --monomorphise \
	    --axiomatize-funcdefs2 \
	    --axiomatize-lambdas --if-to-bool-op \
	    > ../benchmarks-zipper/$$i ; \
	    done

clean:
	find -type d -exec rm -r {} \;

.PHONY: all clean
