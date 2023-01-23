package main;
import "fmt";

func main(){
	fmt.Print(!true)
	fmt.Print("\n")
	fmt.Print(!false)
	fmt.Print("\n")
	fmt.Print(!(3>2))
	fmt.Print("\n")
}

/*
== Expected program output ==
false
true
false
*/