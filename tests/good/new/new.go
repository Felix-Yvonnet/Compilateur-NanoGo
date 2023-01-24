package main;
import "fmt";

type S struct {
	x1 string
}

func main(){
	var t *S = new(S)
	t.x1 = 1
}

/*
== Expected program output ==
*{x1:1}
*/