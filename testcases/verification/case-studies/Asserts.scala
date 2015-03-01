import leon.lang._
import leon.annotation._
import leon.collection._
import leon._

/* 
 This example aims to illustrate use of asserts instead of ensuring
  which should work since Leon also unfolds bodies, 
  since unfolded postconditions are treated (they should also be treated as assume-s.

 At the moment the example also exhibits an internal error, possibly because xlang
 desugaring introduces implication and the phases expect it to have been elimianted.
 */

object Asserts {

  def assert(p: Boolean): Unit = {  // we might define assert like so
    require(p)
  } ensuring(res => p)

  def sum(to: BigInt): BigInt = {
    var i: BigInt = 0
    var s: BigInt = 0
    while (i < to) {
      s= s + i
      i= i + BigInt(1)
    }
    assert(s >= BigInt(1))   // use assert instead of ensuring, like so
    s
  }

/* //Uncomenting this function leads to a crash
  def test = {
    sum(0)
  } ensuring (res => res > 0)
 */
/*
[  Info  ]  - Now considering 'postcondition' VC for assert @11:21...
[  Info  ]    => VALID
[  Info  ]  - Now considering 'precondition' VC for sum @20:5...
[ Error  ]    => INVALID
[ Error  ] Found counter-example : 
[ Error  ] s -> BigInt(0)
[  Info  ]  - Now considering 'postcondition' VC for test @26:22...
[Warning ] Can't handle this in translation to Z3: locally {
             var i = BigInt(0)
             locally {
               var s = BigInt(0)
               {
                 while((i < to)) {
                   {
                     s = (s + i);
                     i = (i + BigInt(1));
                   }
                 }
                 assert(s >= BigInt(1))
                 s
               }
             }
           }
[ Fatal  ] Failed to translate start3 ==> (sum(to) == locally {
             var i = BigInt(0)
             locally {
               var s = BigInt(0)
               {
                 while((i < to)) {
                   {
                     s = (s + i);
                     i = (i + BigInt(1));
                   }
                 }
                 assert(s >= BigInt(1))
                 s
               }
             }
           }) to z3 (class leon.purescala.Trees$Implies)
 */
}
