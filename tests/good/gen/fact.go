package main;

func fact ( n int ) int {
	if n <= 1 {
		return 1 ;
	}
	return n*fact (n-1);
}


func main () {
	fmt.Print("5! = ",fact(5))
	}

/*
== Expected compiler output ==

*/
