package main;
import "fmt";

type T struct { a,b int }

func foo (t T) { t.a = t.a + 1; t.b = t.b + 1 ;}
func bar (t T) { t.a = t.a + 1; t.b = t.b + 1 ;}

func main () {
	var t T
	t.a = 1
	t.b = 2
	fmt.Print(t.a, t.b, "\n");
	foo(t)
	fmt.Print(t.a, t.b, "\n");
	bar(t)
	fmt.Print(t.a, t.b, "\n");
}

/*
== Expected compiler output ==
*/

/*
Bon là on va pas essayer de voir le program output vu que var t T segfault...
*/
