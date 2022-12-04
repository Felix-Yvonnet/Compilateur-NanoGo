package main;

type S struct {
	x int
	x string
};

func main(){}



/*
== Expected compiler output ==
File "./tests/bad/struct/multiple_fields_def.go", line 3, characters 5-6:
error: In S structure, x already defined
*/