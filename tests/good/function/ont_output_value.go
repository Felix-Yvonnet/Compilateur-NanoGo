package main
import "fmt";

func f (b bool) int {
	if b {
        return 1
    } else {
        return 0
    }
}

func main(){
	var z = false
	fmt.Print(f(z), f(!z))
	fmt.Print("\n")
}

/*
== Expected program output ==
01
*/
