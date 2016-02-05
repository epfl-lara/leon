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


  def internalTransfer(): Unit = {
    var checking: BigInt = 0
    var saving: BigInt = 0

    def balance = checking + saving

    def balanceInvariant: Boolean = balance >= 0

    def deposit(x: BigInt): Unit = {
      require(balanceInvariant && x >= 0)
      checking += x
    } ensuring(_ => checking == old(checking) + x && balanceInvariant)

    def withdrawal(x: BigInt): Unit = {
      require(balanceInvariant && x >= 0 && x <= checking)
      checking -= x
    } ensuring(_ => checking == old(checking) - x && balanceInvariant)

    def checkingToSaving(x: BigInt): Unit = {
      require(balanceInvariant && x >= 0 && checking >= x)
      checking -= x
      saving += x
    } ensuring(_ => checking + saving == old(checking) + old(saving) && balanceInvariant)

    deposit(50)
    withdrawal(30)
    checkingToSaving(10)
  }

}
