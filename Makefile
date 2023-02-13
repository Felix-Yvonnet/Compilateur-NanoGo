
EXE=_build/default/main.exe

all: $(EXE)

$(EXE): *.ml* rapport
	dune build @all
	cp $(EXE) ngoc

test: $(EXE) test.go
	./ngoc --debug test.go
	gcc -g -no-pie test.s -o test
	./test
	go run test.go

rapport:
	pdflatex rapport.tex
	rm -rf rapport.log rapport.aux

export-%:
	cp test.go ../tests/exec/$*.go
	go run test.go > ../tests/exec/$*.out

.PHONY: clean
clean:
	dune clean
	rm -rf rapport.pdf
