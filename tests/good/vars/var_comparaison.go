package main
import "fmt";

func main(){
	var z,q, a = false, "Hello", 5
	var x,t,y = true, "hello", 2
	fmt.Print(q == t, q != "a", x || z, z && x, y == a, a != y)
}

/*
== Expected program output ==
false true true false false true
*/
