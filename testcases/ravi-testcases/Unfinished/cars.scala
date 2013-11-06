object Cars {
  
  def cars(x1: Int, x2: Int, x3 : Int, v1: Int, v2: Int, v3: Int) : Int ={
    require(x1 > x2 && x2 > x3)
    
    if(2*v2 == v1 + v3){
      v2
    }      
    if(2* x2 > x1 + x3) {
      cars(x1+v1,x2+v2,x3+v3,v1,v2-1,v3)
    }
    else {
      cars(x1+v1,x2+v2,x3+v3,v1,v2+1,v3)
    }
  } ensuring(res => x1+v1 > x2+res && x2+res > x3+v3)  
}