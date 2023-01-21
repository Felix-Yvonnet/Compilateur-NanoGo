package main
import "fmt"

func main () {
	if true {
		return true;
	}
}

/*
== Expected compiler output ==
File "./tests/bad/loops/if_loops.go", line 6, characters 2-13:
error: too many returned values
*/