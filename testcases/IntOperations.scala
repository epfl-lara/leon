object IntOperations {
    def sum(a: Int, b: Int) : Int = {
        require(b >= 0)
        a + b
    } ensuring(_ >= a)
}
