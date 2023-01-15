package main;
import "fmt";

func main(){
	fmt.Print(!true)
	fmt.Print(!false)
	fmt.Print(!(3>2))
}

/*
== Expected program output ==
false
true
false
*/