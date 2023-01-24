package main;
import "fmt";

func fact ( n int ) int {
	if n <= 1 {
		return 1 ;
	}
	return n*fact (n-1);
}


func main () {
	fmt.Print("5! = ",fact(5),"\n")
	}

/*
== Expected program output ==
5! = 120
*/
