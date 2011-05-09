import scala.collection.immutable.Set
import funcheck.Utils._
import funcheck.Annotations._

object MutuallyRecursive {
	def f(n : Int) : Int = {
		if(n == 0){
			1
		}
		else{
			f(n-1) + g(n-1)
		}
	}

	def g(n : Int) : Int = {
		if(n == 0)
			1
		else
			f(n-1) 
	}ensuring(_ == fib(n + 1))

	def fib(n : Int ) : Int = {
		if(n == 0)
			0
		else
			if(n == 1)
				1
			else
				fib(n-1) + fib (n-2)
	}
}
