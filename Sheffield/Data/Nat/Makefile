literate : Factorial.pdf LargerPrime.pdf

%.pdf : %.lagda
	pdflatex \\input{$<}

tex-clean:
	rm -f *.aux *.log *.out 

tex-realclean:
	rm -f *.aux *.log *.out *.pdf


