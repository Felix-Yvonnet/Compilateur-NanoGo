package main
import "fmt";

func main(){
	sum := 0
	i := 0
	for i < 5 {
		sum = sum + i
		fmt.Print(sum)
		i++
	}
	fmt.Print(sum)
}

/*
== Expected program output ==
10
*/
