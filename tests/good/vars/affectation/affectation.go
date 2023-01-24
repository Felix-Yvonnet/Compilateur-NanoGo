package main
import "fmt";

func main(){
	var z,y = 3,4
	z,y = y,z
	fmt.Print(y,z,"\n")
}

/*
== Expected program output ==
34
*/
