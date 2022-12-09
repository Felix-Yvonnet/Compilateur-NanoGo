package main;

func fact ( n int ) int {
	n = 2
	return true
}



func main () {
	}

/*
== Expected compiler output ==
File "./tests/bad/func/return/return_type.go", line 5, characters 8-12:
error: Wrong type, expected int got bool
*/
