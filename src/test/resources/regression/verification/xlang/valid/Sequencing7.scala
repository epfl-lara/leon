package test.resources.regression.verification.xlang.valid

object Sequencing7 {


  def test(): Int = {
    var x = 5

    {x = x + 1; x}
    {x = x * 2; x}
    {x = x - 1; x}

    x

  } ensuring(res => res == 11)

}
