package main;

func fact ( n int ) int {
	n = 2
	return true
}



func main () {
	}

/*
== Expected compiler output ==
File "./tests/bad/func/return/return_type.go", line 5, characters 1-12:
error: This expression has type 'bool' but an expression of type 'int' was expected
*/
