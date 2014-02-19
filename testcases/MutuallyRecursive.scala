import scala.collection.immutable.Set
import leon.lang._
import leon.annotation._

object MutuallyRecursive {
    def f(n : Int) : Int = {
        if(n <= 0){
            1
        }
        else{
            f(n-1) + g(n-1)
        }
    }

    def g(n : Int) : Int = {
        if(n <= 0)
            1
        else
            f(n-1) 
    }ensuring(_ == fib(n + 1))

    def fib(n : Int ) : Int = {
                    if(n <= 2)
                                    1
                    else
                                    fib(n-1) + fib (n-2)
    }
}
