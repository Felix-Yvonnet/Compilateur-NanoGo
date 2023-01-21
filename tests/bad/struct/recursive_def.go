package main;

type S struct {
	x1 S;
	x2 int;
};

func main(){}

/*
== Expected compiler output ==
File "./tests/bad/struct/recursive_def.go", line 0, characters -1--1:
error: cyclic definition:
	structure 'S' has field of type 'S'
*/