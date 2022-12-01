package main;

type S struct {
	x1 int
	x2 int
};

type S struct {
	x3 int
	x4 int
};

/*
== Expected compiler output ==
File "./tests/bad/struct/multiple_struct_def.go", line 8, characters 5-6:
error: Structure S already defined
*/
