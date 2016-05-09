import random

for i in range(1000,11000,1000):
	print("val ls" + str(i) + ": List = ", end="")
	for j in range(i):
		print("Cons(" + str(random.randint(0,9)) + ", ", end="")
	print("Nil()", end="")
	print(")"*i)
	print("println(\""+ str(i) + " \" + sorttimerec(ls" +  str(i) + "))") 


#val ls2: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()
#println("10 " + sorttimerec(ls))
