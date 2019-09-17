compiler: parser.cpp scanner.cpp 
	$(CXX) -g -O0 -o $@ $^

scanner.cpp: scanner.lpp parser.cpp
	flex -o$@ $<

parser.cpp: parser.ypp
	bison --defines=parser.h -v -o $@ $<

clean:
	rm -f \
		scanner.cpp  \
		parser.h  \
		parser.cpp  \
		parser.output  \
		parser.tab.*  \
		compiler  \
		*.slc.* \
		;


.PHONY: clean
