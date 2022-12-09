package main

type S struct {
	x1 S;
	x2 int;
};


func main(){}

/*
== Expected compiler output ==
File "./tests/good/struct/recursive_def.go", line 3, characters 5-6:
error: Recursive function definition is forbidden
*/