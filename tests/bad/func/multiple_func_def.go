package main;

func fact ( n int ) int {
if n <= 1 {
return 1 ;
}
return n*fact (n-1);
}

func fact ( n int ) int {
if n <= 1 {
return 1 ;
}
return n*fact (n-1);
}

func main () {
}

/*
== Expected compiler output ==
File "./tests/bad/func/multiple_func_def.go", line 6, characters 5-6:
error Function f already defined
*/
