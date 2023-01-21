package main
import "fmt";

func main(){
	var x = 1
	{
		var x = 2
		fmt.Print("\tx =",x)
	}
	fmt.Print("x =",x)
}

/*
== Expected program output ==
	x = 2
x = 1
*/
