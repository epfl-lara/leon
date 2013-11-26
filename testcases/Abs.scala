object Abs {

  def abs(x: Int): Int = (if(x < 0) -x else x) ensuring(_ >= 0)

}
