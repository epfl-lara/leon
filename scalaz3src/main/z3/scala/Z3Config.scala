package z3.scala

import z3.{Z3Wrapper,Pointer}

sealed class Z3Config(params: (String,Any)*) {
  val ptr : Long = Z3Wrapper.mkConfig()

  for((k,v) <- params) {
    Z3Wrapper.setParamValue(this.ptr, k, v.toString)
  }

  def delete() : Unit = {
    Z3Wrapper.delConfig(this.ptr)
  }

  def setParamValue(paramID: String, paramValue: String) : Z3Config = {
    Z3Wrapper.setParamValue(this.ptr, paramID, paramValue)
    this
  }
}
