package main;

func fact ( n int, n string ) int {
	if n <= 1 {
		return 1 ;
	}
	return n*fact (n-1);
}

func main () {
	}

/*
== Expected compiler output ==
File "./tests/bad/func/params/multiple_input_name.go", line 3, characters 19-20:
error: function 'fact': redefinition of parameter 'n'
*/