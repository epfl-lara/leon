import leon.lang._

object BankTransfer {

  case class BankAccount(var checking: BigInt, var saving: BigInt) {
    require(checking >= 0 && saving >= 0)

    def balance: BigInt = checking + saving
  }

  //TODO: support for map references to mutable items
  //case class Bank(accounts: Map[BigInt, BankAccount])


  def deposit(x: BigInt, account: BankAccount): Unit = {
    require(x > 0)
    account.checking = account.checking + x
  } ensuring(_ => account.balance == old(account).balance + x)

  def withdrawal(x: BigInt, account: BankAccount): Unit = {
    require(x > 0 && account.checking >= x)
    account.checking = account.checking - x
  } ensuring(_ => account.balance == old(account).balance - x)

  def transfer(x: BigInt, a1: BankAccount, a2: BankAccount): Unit = {
    require(x > 0 && a1.checking >= x)
    withdrawal(x, a1)
    deposit(x, a2)
  } ensuring(_ => a1.balance + a2.balance == old(a1).balance + old(a2).balance &&
                  a1.balance == old(a1).balance - x &&
                  a2.balance == old(a2).balance + x)


  def save(x: BigInt, account: BankAccount): Unit = {
    require(x > 0 && account.checking >= x)
    account.checking = account.checking - x
    account.saving = account.saving + x
  } ensuring(_ => account.balance == old(account).balance)

}
