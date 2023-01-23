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
	var z = false
	fmt.Print(f(z),f(!z))
	fmt.Print("\n")
}

/*
== Expected program output ==
TrueFalse01
*/
