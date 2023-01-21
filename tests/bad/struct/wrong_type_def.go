package main;

type S struct {
	x3 s;
	x4 int;
};

/*
== Expected compiler output ==
File "./tests/bad/struct/wrong_type_def.go", line 4, characters 4-5:
error: unknown type 's'
*/