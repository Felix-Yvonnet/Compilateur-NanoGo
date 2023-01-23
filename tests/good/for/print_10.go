package main
import "fmt";

func main(){
	sum := 0
	for i := 0; i < 5; i++ {
		sum = sum + i
	}
	fmt.Print(sum)
	fmt.Print("\n")
}

/*
== Expected program output ==
10
*/
