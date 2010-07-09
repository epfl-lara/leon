//SJ: I tried to modify this so that funcheck doesn't give Z3 translation 
//    warnings, but didn't manage quite yet

import scala.collection.immutable.Set

object RedBlack {

  abstract sealed class Color;
  case class Red() extends Color;
  case class Black() extends Color;

  abstract sealed class Tree;
  case class Leaf() extends Tree;
  case class Node(color : Color, left: Tree, elem: Int, right: Tree) extends Tree;

  // Invariant 1. No red node has a red parent
  def invariant1(t: Tree): Boolean = t match {
    case Leaf() => true
    case Node(color, left, _, right) => color match {
      case Black() => invariant1(left) && invariant1(right)
      case Red() => left match {
        case Node(col2, _, _, _) => col2 match {
	  case Red() => false
	  case _ => right match {
	    case Node(col3, _, _, _) => col3 match {
	      case Red() => false
	      case _ => invariant1(left) && invariant1(right)
            }
          }
        }
        case Leaf() => right match {
	    case Node(col3, _, _, _) => col3 match {
	      case Red() => false
	      case _ => invariant1(left) && invariant1(right)
            }
        }
      }
    }
  }
  /// Invariant 1 END

  // Invariant 2. Each path from the root to an
  // empty node contains the same number of black
  // nodes
  
  def countBlackNodes(t: Tree): Int = t match {
    case Leaf() => 1
    case Node(color, left, _, _) => color match {
      case Red() => countBlackNodes(left)
      case Black() => countBlackNodes(left) + 1
    }
  }

  def invariant2(t: Tree, n: Int): Boolean = t match {
    case Leaf() => if (n == 1) true else false
    case Node(color, left, _, right) => color match {
      case Red() => invariant2(left, n) && invariant2(right, n)
      case Black() => invariant2(left, n-1) && invariant2(right, n-1)
    }
  }

  /// Invariant 2 END

  def member(t: Tree, e: Int): Boolean = t match {
    case Leaf() => false
    case Node(_, left, x, right) => if (x == e) true
    	 	       	  	    else if (e < x) member( left, e)
    				    else member(right, e)
  }

  def contents(t: Tree): Set[Int] = t match {
    case Leaf() => Set.empty
    case Node(_, left, x, right) => contents(left) ++ contents(right) ++ Set(x)
  }

  def makeBlack(t: Node) = {
    //require(t != Leaf())
    //val Node(_, left, x, right) = t 
    //Node(Black(), left, x, right)
    Node(Black(), t.left, t.elem, t.right)
  } ensuring ((x:Tree) => x match {case Node(col, _, _, _) => (col==Black()); case _ => false})

  def ins_(t: Tree, e: Int): Node = t match {
    case Leaf() => Node(Red(), Leaf(), e, Leaf())
    case n@Node(color, left, x, right) => if (x<e) balance(Node(color, ins_(left, e), x, right))
                                        else if (x > e) balance(Node(color, left, x, ins_(right, e)))
					else n //Element already exists
  }

//  def balance(t: Node) : Node =  {
    //require(t != Leaf())
//    t match {
//      case Node(Black(), Node(Red(), Node(Red(), a, x, b), y, c), z, d) => Node(Red(), Node(Black(), a, x, b), y, Node(Black(), c, z, d))
//      case Node(Black(), Node(Red(), a, x, Node(Red(), b, y, c)), z, d) => Node(Red(), Node(Black(), a, x, b), y, Node(Black(), c, z, d))
//      case Node(Black(), a, x, Node(Red(), Node(Red(), b, y, c), z, d)) => Node(Red(), Node(Black(), a, x, b), y, Node(Black(), c, z, d))
//      case Node(Black(), a, x, Node(Red(), b, y, Node(Red(), c, z, d))) => Node(Red(), Node(Black(), a, x, b), y, Node(Black(), c, z, d))
//      case n@Node(_,_,_,_) => n
//    }
//  } //ensuring (_ => true)

  def balance(t: Node) : Node =  {
    //require(t != Leaf())
    t.color match {
      case Black() => t.left match {
        case Node(cl,ll,el,rl) => cl match {
	  case Red() => ll match {
	    case Node(cll,lll,ell,rll) => cll match {
	      case Red() => Node(Red(), Node(Black(), lll, ell, rll), el, Node(Black(), rl, t.elem, t.right))
	      case Black() => rl match {
		case Node(crl,lrl,erl,rrl) => crl match {
		  case Red() => Node(Red(), Node(Black(), ll, el, lrl), erl, Node(Black(), rrl, t.elem, t.right))
		  case Black() => t.right match {
		    case Node(cr,lr,er,rr) => cr match {
 		      case Red() => lr match {
		        case Node(clr,llr,elr,rlr) => clr match {
			  case Red() => Node(Red(), Node(Black(), t.left, t.elem, llr), elr, Node(Black(), rlr, er, rr))
                          case Black() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			  }
		        case Leaf() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			}
		      case Black() => t
		      }
		    case Leaf() => t
		    }
		  }
		case Leaf() => t.right match {
		    case Node(cr,lr,er,rr) => cr match {
 		      case Red() => lr match {
		        case Node(clr,llr,elr,rlr) => clr match {
			  case Red() => Node(Red(), Node(Black(), t.left, t.elem, llr), elr, Node(Black(), rlr, er, rr))
                          case Black() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			  }
		        case Leaf() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			}
		      case Black() => t
		      }
		    case Leaf() => t
		    }
		}
	      }
	    case Leaf() => rl match {
		case Node(crl,lrl,erl,rrl) => crl match {
		  case Red() => Node(Red(), Node(Black(), ll, el, lrl), erl, Node(Black(), rrl, t.elem, t.right))
		  case Black() => t.right match {
		    case Node(cr,lr,er,rr) => cr match {
 		      case Red() => lr match {
		        case Node(clr,llr,elr,rlr) => clr match {
			  case Red() => Node(Red(), Node(Black(), t.left, t.elem, llr), elr, Node(Black(), rlr, er, rr))
                          case Black() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			  }
		        case Leaf() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			}
		      case Black() => t
		      }
		    case Leaf() => t
		    }
		  }
		case Leaf() => t.right match {
		    case Node(cr,lr,er,rr) => cr match {
 		      case Red() => lr match {
		        case Node(clr,llr,elr,rlr) => clr match {
			  case Red() => Node(Red(), Node(Black(), t.left, t.elem, llr), elr, Node(Black(), rlr, er, rr))
                          case Black() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			  }
		        case Leaf() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			}
		      case Black() => t
		      }
		    case Leaf() => t
		    }
		}
	    }
	  case Black() => t.right match {
		    case Node(cr,lr,er,rr) => cr match {
 		      case Red() => lr match {
		        case Node(clr,llr,elr,rlr) => clr match {
			  case Red() => Node(Red(), Node(Black(), t.left, t.elem, llr), elr, Node(Black(), rlr, er, rr))
                          case Black() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			  }
		        case Leaf() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			}
		      case Black() => t
		      }
		    case Leaf() => t
		    }
	  }
      	case Leaf() => t.right match {
		    case Node(cr,lr,er,rr) => cr match {
 		      case Red() => lr match {
		        case Node(clr,llr,elr,rlr) => clr match {
			  case Red() => Node(Red(), Node(Black(), t.left, t.elem, llr), elr, Node(Black(), rlr, er, rr))
                          case Black() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			  }
		        case Leaf() => rr match {
			    case Node(crr,lrr,err,rrr) => crr match {
			      case Red() => Node(Red(), Node(Black(), t.left, t.elem, lr), er, Node(Black(), lrr, err, rrr))
			      case Black() => t
			      }
			    case Leaf() => t
			    }
			}
		      case Black() => t
		      }
		    case Leaf() => t
		    }
      	}
      case Red() => t
      }
    }

  def insert(t: Tree, e: Int): Tree = makeBlack( ins_(t, e) ) ensuring {res => invariant1(res) && invariant2(res, countBlackNodes(res))}

  def main(args : Array[String]) = {
    var rb : Tree = Leaf()
    for(ii <- 1 to 10) {
      rb = insert( rb, ii )
      println(rb)
    }
  }
}
  

