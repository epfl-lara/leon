import scala.collection.immutable.Set

object Nasty {
  def vc6a(l1 : Int, nul : Int, ths : Int, tmp357 : Int, list : Set[Int], objct : Set[Int], objAlloc : Set[Int], objAlloc16 : Set[Int], objAlloc30 : Set[Int], objAlloc45 : Set[Int], objAlloc60 : Set[Int], objAlloc74 : Set[Int], listContent : Set[Int], listContent59 : Set[Int], listContent73 : Set[Int], s241 : Set[Int], s142 : Set[Int], tmp171 : Boolean) : Set[Int] = {
    require(
      l1 != nul
   && l1 != ths
   && ths != nul
   && list.contains(ths)
   && objAlloc.contains(ths)
   && list.contains(l1)
   && objAlloc.contains(l1)
   && objAlloc74 == objAlloc
   && listContent73 == listContent
   && (objAlloc subsetOf objAlloc74)
   && !tmp171
   && objAlloc60 == objAlloc74
   && listContent59 == listContent73
   && (objAlloc74 subsetOf objAlloc60)
   && objct.contains(tmp357)
   && objAlloc60.contains(tmp357)
   && objAlloc45 == objAlloc60
   && (objAlloc60 subsetOf objAlloc45)
   && objAlloc45 == objAlloc
   && s142.contains(tmp357)
   && s241 == s142 -- Set(tmp357)
   && (objAlloc30 -- objAlloc45).size <= 1
   && (objAlloc45 subsetOf objAlloc30)
   && (objAlloc30 -- objAlloc).size <= 1
   && (objAlloc30 subsetOf objAlloc16)
   && (objAlloc16 -- objAlloc30).size <= s241.size
    )
    objAlloc16 -- objAlloc
  } ensuring(_.size <= s142.size)

  def vc6ar(l1 : Set[Int], nul : Set[Int], ths : Set[Int], tmp357 : Set[Int], list : Set[Int], objct : Set[Int], objAlloc : Set[Int], objAlloc16 : Set[Int], objAlloc30 : Set[Int], objAlloc45 : Set[Int], objAlloc60 : Set[Int], objAlloc74 : Set[Int], listContent : Set[Int], listContent59 : Set[Int], listContent73 : Set[Int], s241 : Set[Int], s142 : Set[Int], tmp171 : Boolean) : Set[Int] = {
    require(
      l1.size == 1
   && nul.size == 1
   && ths.size == 1
   && tmp357.size == 1
   && l1 != nul
   && l1 != ths
   && ths != nul
   && (ths subsetOf list)
   && (ths subsetOf objAlloc)
   && (l1 subsetOf list)
   && (l1 subsetOf objAlloc)
   && objAlloc74 == objAlloc
   && listContent73 == listContent
   && (objAlloc subsetOf objAlloc74)
   && !tmp171
   && objAlloc60 == objAlloc74
   && listContent59 == listContent73
   && (objAlloc74 subsetOf objAlloc60)
   && (tmp357 subsetOf objct)
   && (tmp357 subsetOf objAlloc60)
   && objAlloc45 == objAlloc60
   && (objAlloc60 subsetOf objAlloc45)
   && objAlloc45 == objAlloc
   && (tmp357 subsetOf s142)
   && s241 == s142 -- tmp357
   && (objAlloc30 -- objAlloc45).size <= 1
   && (objAlloc45 subsetOf objAlloc30)
   && (objAlloc30 -- objAlloc).size <= 1
   && (objAlloc30 subsetOf objAlloc16)
   && (objAlloc16 -- objAlloc30).size <= s241.size
    )
    objAlloc16 -- objAlloc
  } ensuring(_.size <= s142.size)

  def vc6dr(l1 : Set[Int], nul : Set[Int], ths : Set[Int], tmp357 : Set[Int], list : Set[Int], objct : Set[Int], objAlloc : Set[Int], objAlloc16 : Set[Int], objAlloc30 : Set[Int], objAlloc45 : Set[Int], objAlloc60 : Set[Int], objAlloc74 : Set[Int], /*listContent : Set[Int], listContent59 : Set[Int], listContent73 : Set[Int],*/ s241 : Set[Int], s142 : Set[Int], tmp171 : Boolean) : Set[Int] = {
    require(
      l1.size == 1
   && nul.size == 1
   && ths.size == 1
   && tmp357.size == 1
   && l1 != nul
   && l1 != ths
   && ths != nul
   && (ths subsetOf list)
   && (ths subsetOf objAlloc)
   && (l1 subsetOf list)
   && (l1 subsetOf objAlloc)
   && objAlloc74 == objAlloc
   // && listContent73 == listContent
   && (objAlloc subsetOf objAlloc74)
   && !tmp171
   && objAlloc60 == objAlloc74
   // && listContent59 == listContent73
   && (objAlloc74 subsetOf objAlloc60)
   && (tmp357 subsetOf objct)
   && (tmp357 subsetOf objAlloc60)
   && objAlloc45 == objAlloc60
   && (objAlloc60 subsetOf objAlloc45)
   && objAlloc45 == objAlloc
   && (tmp357 subsetOf s142)
   && s241 == s142 -- tmp357
   && (objAlloc30 -- objAlloc45).size <= 1
   && (objAlloc45 subsetOf objAlloc30)
   && (objAlloc30 -- objAlloc).size <= 1
   && (objAlloc30 subsetOf objAlloc16)
   && (objAlloc16 -- objAlloc30).size <= s241.size
    )
    objAlloc16 -- objAlloc
  } ensuring(_.size <= s142.size)
}
