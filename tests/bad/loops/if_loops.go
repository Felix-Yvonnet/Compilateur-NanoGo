package main
import "fmt"

func main () {
	if true {
		return true;
	}
}

/*
== Expected compiler output ==
File "./tests/bad/loops/if_loops.go", line 6, characters 9-13:
error: Function expect 0 outputs but got 1
*/