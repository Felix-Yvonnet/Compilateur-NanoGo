package main
import "fmt";

func f (b bool) int {
	if b {
		fmt.Print("True")
		return 1
	} else {
		fmt.Print("False")
		return 0
	}
}

func main(){
	var z,t = f(true), f(false)
	fmt.Print(z,t,"\n")
}

/*
== Expected program output ==
TrueFalse10
*/
