package main;

func fact ( n int ) int {
	if n <= 1 {
		return 1 ;
	}
}


func main () {
	}

/*
== Expected compiler output ==
File "./tests/bad/func/return/missing_return_if.go", line 3, characters 5-9:
error: missing return statements for function 'fact'
*/
