object IntOperations {
    def sum(a: Int, b: Int) : Int = {
        a + (if(b < 0) -b else b)
    } ensuring(_ >= a)

}
