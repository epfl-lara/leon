object TestProgram
{
	def func1(x: Int) : Boolean = {
			val y = func2(x)
			(y * 10 <= 100)
	} 
	
	def func2(x: Int) : Int = {
			(x + 1)
	} ensuring(res => !func1(x) || res <= 5)       
} 