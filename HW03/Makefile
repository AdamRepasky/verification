# List all formulae in your model by "$ nuXmv -lp your.smv".
# Assign the indices of the formulae corresponding to the 
# properties P1, P2, ...
P1=000
P2=001
P3=002
P4=003
P5=004
P6=005
P7=006
P8=007
P9=008
P10=

# If your formulae are negations of the required properties,
# leave the corresponding P above empty and assign the index
# to the right N below.
N1=
N2=
N3=
N4=
N5=
N6=
N7=
N8=
N9=
N10=009


.SECONDARY:

# Fill in you command transforming *.csv files to *.smv.
# If you run it as $ my_script -myparam file.csv use:
# TRANS_CSV2SMV_COMMAND=my_script -myparam
TRANS_CSV2SMV_COMMAND=my_script -myparam
# or edit the rules for target %.smv

NUXMV_COMMAND=nuXmv
# or NUXMV_COMMAND=nuXmv -cpp .

ALL_SOL_FILES=$(wildcard *.sol)

%.smv: %.csv
	${TRANS_CSV2SMV_COMMAND} $<

%.results: %.smv
	cp /dev/null $@; \
	COUNT=0; \
	for idx in "${P1}" "${P2}" "${P3}" "${P4}" "${P5}" "${P6}" "${P7}" "${P8}" "${P9}" "${P10}";  do \
	    COUNT=$$((COUNT + 1)); \
	    if [ ! -z "$$idx" ]; then \
	        printf "P%02d: " $${COUNT} >>$@; \
	        ${NUXMV_COMMAND} -n $$idx $< | grep -- "^-- specification" | sed "s/-- specification.*is //g" >>$@; \
	    fi; \
	done; \
	COUNT=0; \
	for idx in "${N1}" "${N2}" "${N3}" "${N4}" "${N5}" "${N6}" "${N7}" "${N8}" "${N9}" "${N10}";  do \
	    COUNT=$$((COUNT + 1)); \
	    if [ ! -z "$$idx" ]; then \
	        printf "N%02d: " $${COUNT} >>$@; \
	        ${NUXMV_COMMAND} -n $$idx $< | grep -- "^-- specification" | sed "s/-- specification.*is //g" >>$@; \
	    fi; \
	done;

# for all files *.sol compares the results with *.results
test: $(ALL_SOL_FILES:.sol=.comp)
	@echo "Checking all..."

# individual comparisons
%.comp: %.results %.sol
	@sed "s/N\(.*\): true/P\1: false/" $< | \
	sed "s/N\(.*\): false/P\1: true/" | sort | uniq >$(<:.results=.ressort) ;\
	diff $(<:.results=.ressort) $(<:.results=.sol) >$@ 2>&1 || echo "The results differ for $(<:.results=.smv). See $<."

clean:
	rm -f *.results *.ressort *.smv *.comp
