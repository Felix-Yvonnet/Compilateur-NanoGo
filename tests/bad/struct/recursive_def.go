package main;

type S struct {
	x1 S;
	x2 int;
};

/*
== Expected compiler output ==
File "./tests/bad/struct/recursive_def.go", line 3, characters 5-6:
error: Recursive structure definition is forbidden
*/