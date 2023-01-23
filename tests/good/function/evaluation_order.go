package main
import "fmt";

func foo1 () bool {
	fmt.Print(true)
	return true
}

func foo2 () bool {
	fmt.Print(false)
	return false
}

func f (b1,b2 bool) {
	return
}

func main(){
	f(foo1(),foo2())
	fmt.Print("\n")
}

/*
== Expected program output ==
falsetrue
*/
