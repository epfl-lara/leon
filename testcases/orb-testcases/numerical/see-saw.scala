object SeeSaw {
  def s(x: BigInt, y: BigInt, z: BigInt): BigInt = {
    require(y >= 0)

    if (x >= 100) {
      y
    } else if (x <= z) { //some condition
      s(x + 1, y + 2, z)
    } else if (x <= z + 9) { //some condition
      s(x + 1, y + 3, z)
    } else {
      s(x + 2, y + 1, z)
    }
  } ensuring (res => (100 - x <= 2 * res))
}