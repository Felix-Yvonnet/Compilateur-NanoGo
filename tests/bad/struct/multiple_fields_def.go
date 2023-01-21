package main;

type S struct {
	x int;
	x string;
};

func main(){}



/*
== Expected compiler output ==
File "./tests/bad/struct/multiple_fields_def.go", line 5, characters 1-2:
error: structure 'S': redefinition of field 'x'
*/