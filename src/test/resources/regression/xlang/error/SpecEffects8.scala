import leon.lang._

object SpecEffects8 {


  def veryFoo(): Unit = {

    var i = 0

    def incI = {
      i+=1
      i
    }

    def rec(): Unit = {
      if(i < 10) {
        i += 1
        rec()
      }
    } ensuring(_ => incI >= 0)

    rec()

    assert(i == 10)
  }

}
