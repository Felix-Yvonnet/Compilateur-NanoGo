package main;
import "fmt";

type S struct {
	x1 string
}

func main(){
	var t *S = new(S)
	fmt.Print(t)
}

/*
*/