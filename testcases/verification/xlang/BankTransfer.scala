import leon.lang._

object BankTransfer {

  def okTransaction(): Unit = {
    var balance: BigInt = 0

    def balanceInvariant: Boolean = balance >= 0

    def deposit(x: BigInt): Unit = {
      require(balanceInvariant && x >= 0)
      balance += x
    } ensuring(_ => balance == old(balance) + x && balanceInvariant)

    def withdrawal(x: BigInt): Unit = {
      require(balanceInvariant && x >= 0 && x <= balance)
      balance -= x
    } ensuring(_ => balance == old(balance) - x && balanceInvariant)

    deposit(35)
    withdrawal(30)
  }

  def invalidTransaction(): Unit = {
    var balance: BigInt = 0

    def balanceInvariant: Boolean = balance >= 0

    def deposit(x: BigInt): Unit = {
      require(balanceInvariant && x >= 0)
      balance += x
    } ensuring(_ => balance == old(balance) + x && balanceInvariant)

    def withdrawal(x: BigInt): Unit = {
      require(balanceInvariant && x >= 0 && x <= balance)
      balance -= x
    } ensuring(_ => balance == old(balance) - x && balanceInvariant)

    deposit(35)
    withdrawal(40)
  }
}
