package setconstraints

import Trees._
import Manip._
import Tools._

object Solver {

  def apply(system: Set[Relation], constructors: Map[String, Int]): Option[Map[VariableType, SetType]] = {
    val solvedSystems = solve(system, constructors)
    if(solvedSystems.isEmpty)
      None
    else {
      val sys = solvedSystems.head
      val freeVarsMap = Map(freeVars(sys).map(v => (v, EmptyType)).toSeq: _*)
      val system = sys.map{case Equals(v, s) => Equals(v, simplify(substitute(s, freeVarsMap)))}
      val initMap: Map[VariableType, SetType] = Map(system.map{case Equals(v, _) => (v.asInstanceOf[VariableType], EmptyType)}.toSeq: _*)
      println(system.map(PrettyPrinter(_)))
      Some(fix(
        (m: Map[VariableType, SetType]) => {
          println("new iteration")
          println(m.map{case (v, s) => (PrettyPrinter(v), PrettyPrinter(s))})
          val ns = system.map{case Equals(v, s) => Equals(v, simplify(substitute(s, m)))}
          println(ns.map(PrettyPrinter(_)))
          Map(ns.map{case Equals(v, s) => (v.asInstanceOf[VariableType], s)}.toSeq: _*)
        },
        initMap))
    }
  }

  def solve(system: Set[Relation], constructors: Map[String, Int]): Set[Seq[Equals]] = {
    val includes = system.flatMap(Manip.removeEquals)
    val oneLevelSystem = oneLevel(includes, constructors)
    val decrOrder = decreasingOrder(oneLevelSystem)
    val cascad = cascadingSystems(decrOrder, constructors)
    val cascadEq = cascadingEquations(cascad)
    val remTLV = removeTopLevelVars(cascadEq)
    val solvedSys = solvedForm(remTLV, constructors)
    solvedSys
  }

  def freeVars(system: Seq[Equals]): Set[VariableType] = {
    val bvs = system.map{case Equals(v, _) => v}.toSet
    system.foldLeft(Set[VariableType]())((a, eq) => eq match {
      case Equals(_, s) => a ++ Manip.vars(s).filter((v: String) => !bvs.contains(VariableType(v))).map(VariableType(_))
    })
  }

  def solvedForm(systems: Set[Seq[Equals]], constructors: Map[String, Int]): Set[Seq[Equals]] = {
    def substComp(s: SetType, ov: VariableType, ns: SetType) = mapPostorder(s, {
      case ComplementType(v@VariableType(_)) if v == ov => ns
      case s => s
    })
    def solvedForm(system: Seq[Equals]): Seq[Equals] = {
      val vs: Seq[VariableType] = system.map{case Equals(v@VariableType(_), _) => v case _ => error("not cascading equations")}
      val nvs = vs.map{case VariableType(n) => freshVar(n)}
      def doAllSubst(s: SetType): SetType = vs.zip(nvs).foldLeft(s)((a, p) => p match {
        case (v, nv) => substComp(a, v, nv)
      })
      val nps = system.zip(nvs).map{
        case (Equals(v@VariableType(_), s), nv) => Equals(v, doAllSubst(nnf(s, constructors)))
        case _ => error("not format")
      }
      val nns = system.zip(nvs).map{
        case (Equals(v@VariableType(_), s), nv) => Equals(nv, doAllSubst(nnf(ComplementType(s), constructors)))
        case _ => error("not format")
      }
      val nnns = nns.zipWithIndex.filter{
        case (Equals(VariableType(n), s), i) =>
          nps.exists{case Equals(_, s2) => Manip.vars(s2).exists(_ == n)} ||
          nns.zipWithIndex.exists{case (Equals(_, s2), i2) => i != i2 && Manip.vars(s2).exists(_ == n)}
        case _ => error("unexpected")
      }.unzip._1
      nps ++ nnns
    }
    systems.map(solvedForm)
  }

  def removeTopLevelVars(systems: Set[Seq[Equals]]): Set[Seq[Equals]] = {
    def removeTopLevelVars0(system: Seq[Equals]): Seq[Equals] = {
      def subst(s: SetType, ov: VariableType, eqs: Seq[Equals]) = eqs.find{case Equals(v, _) => v == ov} match {
        case Some(Equals(_, ns)) => mapPreorderWhile(s, {
          case v@VariableType(_) if v == ov => ns
          case s => s
        }, {
          case ConstructorType(_, _) => false
          case _ => true
        })
        case None => s
      }
      system.foldLeft(Seq[Equals]())((initEqs, eq) => eq match {
          case Equals(v, s) => {
            val ns = Manip.vars(s).foldLeft(s)((a, v) => subst(a, VariableType(v), initEqs))
            initEqs :+ Equals(v, ns)
          }
      })
    }
    systems.map(removeTopLevelVars0)
  }

  def cascadingEquations(systems: Set[Set[Include]]): Set[Seq[Equals]] = {
    def cascadingEquations0(system: Set[Include]): Seq[Equals] = {
      val vs = vars(system).toSeq
      val nvs = vs.map(freshVar(_))
      val ts = vs.zip(nvs).map{case (v, nv) => {
        val lb = UnionType(system.flatMap{
          case Include(IntersectionType(lits), EmptyType) if !lits.isEmpty && lits.head == ComplementType(VariableType(v)) => lits.tail
          case _ => Seq()
        }.toSeq)
        val ub = IntersectionType(system.flatMap{
          case Include(IntersectionType(lits), EmptyType) if !lits.isEmpty && lits.head == VariableType(v) => 
            Seq(ComplementType(IntersectionType(lits.tail)))
          case _ => Seq()
        }.toSeq)
        UnionType(Seq(lb, IntersectionType(Seq(nv, ub))))
      }}
      val ns = vs.zip(ts).map{case (v, t) => Equals(VariableType(v), t)}
      val sns = ns.map{case Equals(v, rhs) => Equals(v, simplify(rhs))}
      sns.sortWith((eq1, eq2) => (eq1.s1, eq2.s1) match {
        case (VariableType(v1), VariableType(v2)) => v1 < v2
        case _ => error("no vars as lhs of equals")
      })
    }
    systems.map(cascadingEquations0)
  }

  def cascadingSystems(system: Set[Include], constructors: Map[String, Int]): Set[Set[Include]] = {

    def constructorRule(system: Set[Include]): Set[Set[Include]] = {
      val (option, rest) = extract((x: Include) => x match {
        case Include(IntersectionType(Seq(ConstructorType(_, args))), EmptyType) => true 
        case _ => false
      }, system)
      option match {
        case Some(Include(IntersectionType(Seq(ConstructorType(_, args))), EmptyType)) =>
          args.map(arg => rest + Include(arg, EmptyType)).toSet
        case None => Set(system)
        case _ => error("")
      }
    }

    def transitiveRule(system: Set[Include]): Set[Include] = {
    /*
      val (candidates, r1) = system.partition{
        case Include(IntersectionType(List(VariableType(_), _)), EmptyType) => true
        case _ => false
      }
      val (candidatesNeg, r2) = r1.partition{
        case Include(IntersectionType(List(ComplementType(VariableType(_)), _)), EmptyType) => true
        case _ => false
      }
      val newCnstrs = candidates.flatMap{
        case Include(IntersectionType(List(VariableType(v1), s1)), EmptyType) => {
          candidatesNeg.flatMap{
            case Include(IntersectionType(List(ComplementType(VariableType(v2)), s2)), EmptyType) => {
              if(v1 == v2)
                Set(Include(IntersectionType(List(s1, s2)), EmptyType))
              else
                Nil
            }
            case _ => error("")
          }
        }
        case _ => error("")
      }
      newCnstrs ++ system
      */

      def keepOneLevel(lits1: Seq[SetType], lits2: Seq[SetType]): SetType = {

        def combineConstructors(c1: ConstructorType, c2: ConstructorType): Option[ConstructorType] = (c1, c2) match {
          case (ConstructorType(n1, _), ConstructorType(n2, _)) if n1 != n2 => None
          case (ConstructorType(n, args1), ConstructorType(_, args2)) => {
            val args = args1.zip(args2).map{
              case (IntersectionType(lits1), IntersectionType(lits2)) => combineLits(lits1 ++ lits2)
              case _ => error("not one level")
            }
            if(args.exists{
              case None => true
              case Some(_) => false
            }) None else Some(ConstructorType(n, args.map{
              case Some(lits) => IntersectionType(lits)
              case None => error("no way")
            }))
          }
        }

        def combineLits(lits: Seq[SetType]): Option[Seq[SetType]] = if(lits.exists(_ == EmptyType)) None else if(lits.exists{
            case v@VariableType(_) => lits.exists((s: SetType) => s == ComplementType(v))
            case ComplementType(v@VariableType(_)) => lits.exists((s: SetType) => s == v)
            case _ => false
          }) None else Some(lits)

        (lits1, lits2) match {
          case (Seq(), lits2) => IntersectionType(lits2)
          case (lits1, Seq()) => IntersectionType(lits1)
          case _ => {
            val (init1, last1) = (lits1.init, lits1.last)
            val (init2, last2) = (lits2.init, lits2.last)
            val (lits, constr) = (last1, last2) match {
              case (c1@ConstructorType(_, _), c2@ConstructorType(_, _)) => (init1 ++ init2, combineConstructors(c1, c2))
              case (c@ConstructorType(_, _), s) => (s +: (init1 ++ init2), Some(c))
              case (s, c@ConstructorType(_, _)) => (s +: (init1 ++ init2), Some(c))
              case (s1, s2) => (lits1 ++ lits2, None)
            }
            (combineLits(lits), constr) match {
              case (None, _) => EmptyType
              case (_, None) => EmptyType
              case (Some(lits), Some(c)) => decreasingOrder(IntersectionType(lits :+ c))
            }
          }
        }
      }


/*
      def simp(s1: SetType, s2: SetType): SetType = {
        val res = (s1, s2) match {
          case (EmptyType, _) => EmptyType
          case (_, EmptyType) => EmptyType
          case (v1, ComplementType(v2))) if v1 == v2 => EmptyType
          case (ComplementType(v1), v2) if v1 == v2 => EmptyType
          case (ConstructorType(_, args)) if args.exists(_ == EmptyType) => EmptyType
          case (ConstructorType(n1, _), ConstructorType(n2, _)) if n1 != n2 => EmptyType
          case (ConstructorType(n1, args1), ConstructorType(n2, args2))) =>
            if(n1 != n2) 
              error("unexpected")
            else
              keepOneLevel(IntersectionType(Seq(ConstructorType(n1, args1.zip(args2).map{
                case (IntersectionType(lits1), IntersectionType(lits2)) => simplify(IntersectionType(lits1 ++ lits2)) match {
                  case EmptyType => EmptyType
                  case UniversalType => IntersectionType(Seq())
                  case i@IntersectionType(_) => i
                  case v@VariableType(_) => IntersectionType(Seq(v))
                  case v@ComplementType(VariableType(_)) => IntersectionType(Seq(v))
                  case _ => error("unexpected")
                }
                case _ => error("not one level: " + i)
              }))))
          case _ => s
        }
        decreasingOrder(res)

        val res = (s1, s2) match {
          case IntersectionType(Seq(EmptyType, _)) => EmptyType
          case IntersectionType(Seq(_, EmptyType)) => EmptyType
          case IntersectionType(Seq(v1, ComplementType(v2))) if v1 == v2 => EmptyType
          case IntersectionType(Seq(ComplementType(v1), v2)) if v1 == v2 => EmptyType
          case IntersectionType(Seq(ConstructorType(_, args))) if args.exists(_ == EmptyType) => EmptyType
          case IntersectionType(Seq(ConstructorType(n1, _), ConstructorType(n2, _))) if n1 != n2 => EmptyType
          case i@IntersectionType(Seq(ConstructorType(n1, args1), ConstructorType(n2, args2))) =>
            if(n1 != n2) 
              error("unexpected")
            else
              keepOneLevel(IntersectionType(Seq(ConstructorType(n1, args1.zip(args2).map{
                case (IntersectionType(lits1), IntersectionType(lits2)) => simplify(IntersectionType(lits1 ++ lits2)) match {
                  case EmptyType => EmptyType
                  case UniversalType => IntersectionType(Seq())
                  case i@IntersectionType(_) => i
                  case v@VariableType(_) => IntersectionType(Seq(v))
                  case v@ComplementType(VariableType(_)) => IntersectionType(Seq(v))
                  case _ => error("unexpected")
                }
                case _ => error("not one level: " + i)
              }))))
          case _ => s
        }
        decreasingOrder(res)
      }
        */

      val trans = system.flatMap[Include, Set[Include]]{
        case Include(EmptyType, EmptyType) => Set()
        case i@Include(IntersectionType(Seq()), EmptyType) => Set(i)
        case i@Include(IntersectionType(lits), EmptyType) => lits.head match {
          case ConstructorType(_, _) => Set()
          case v@VariableType(_) => system.flatMap[Include, Set[Include]]{
            case Include(IntersectionType(lits2), EmptyType) => {
              if(!lits2.isEmpty && lits2.head == ComplementType(v))
                Set(Include(
                  keepOneLevel(lits.tail, lits2.tail),
                  EmptyType))
              else Set()
            }
            case _ => Set()
          }
          case ComplementType(v@VariableType(_)) => system.flatMap[Include, Set[Include]]{
            case Include(IntersectionType(lits2), EmptyType) => {
              if(!lits2.isEmpty && lits2.head == v)
                Set(Include(
                  keepOneLevel(lits.tail, lits2.tail),
                  EmptyType))
              else Set()
            }
            case _ => Set()
          }
          case _ => error("not one level")
        }
        case _ => error("not one level")
      }

      trans ++ system
    }

    def iter(systems: Set[Set[Include]]): Set[Set[Include]] = systems.flatMap(system => {
      val trans = transitiveRule(system)
      val constrSystem = constructorRule(trans)
      val consistentSystems: Set[Set[Include]] = constrSystem.filterNot(sys => sys.exists{
        case Include(UniversalType, EmptyType) => true
        case Include(IntersectionType(Seq(ConstructorType(_, Seq()))), EmptyType) => true
        case _ => false
      })
      val res = consistentSystems.map((system: Set[Include]) => system.flatMap[Include, Set[Include]]{
        case Include(EmptyType, EmptyType) => Set()
        case i => Set(i)
      })
      res
    })

    fix(iter, Set(system))
  }

  def decreasingOrder(s: SetType): SetType = {
    def order(s1: SetType, s2: SetType): Boolean = (s1, s2) match {
      case (VariableType(n1), VariableType(n2)) => n1 > n2
      case (ComplementType(VariableType(n1)), VariableType(n2)) => n1 > n2
      case (VariableType(n1), ComplementType(VariableType(n2))) => n1 > n2
      case (ComplementType(VariableType(n1)), ComplementType(VariableType(n2))) => n1 > n2
      case (VariableType(_), ConstructorType(_, _)) => true
      case (ComplementType(VariableType(_)), ConstructorType(_, _)) => true
      case (ConstructorType(_, _), VariableType(_)) => false
      case (ConstructorType(_, _), ComplementType(VariableType(_))) => false
      case _ => error("not one level: " + PrettyPrinter(s1) + " should not have to be compared to " + PrettyPrinter(s2))
    }
    val ns = s match {
      case EmptyType => EmptyType
      case IntersectionType(sts) => IntersectionType(sts.sortWith(order))
      case _ => error("not expected")
    }
    ns
  }
  def decreasingOrder(system: Set[Include]): Set[Include] = system.map{
    case Include(s, EmptyType) => Include(decreasingOrder(s), EmptyType)
    case _ => error("not expected")
  }

  def oneLevel(system: Set[Include], constructors: Map[String, Int]): Set[Include] = {

    def canIntersectionLit(lhs: SetType): Option[SetType] = simplify(lhs) match {
      case UniversalType => Some(IntersectionType(Seq()))
      case v@VariableType(_) => Some(IntersectionType(Seq(v)))
      case c@ComplementType(VariableType(_)) => Some(IntersectionType(Seq(c)))
      case i@IntersectionType(sts) if sts.forall(isLiteral) => Some(i)
      case _ => None
    }
    def canOneLevel(lhs: SetType): Option[SetType] = simplify(lhs) match {
      case e@EmptyType => Some(e)
      case UniversalType => Some(IntersectionType(Seq()))
      case v@VariableType(_) => Some(IntersectionType(Seq(v)))
      case c@ComplementType(VariableType(_)) => Some(IntersectionType(Seq(c)))
      case ConstructorType(n, args) => {
        val oneArgs = args.map(canIntersectionLit)
        if(oneArgs.forall(_ != None))
          Some(IntersectionType(Seq(ConstructorType(n, oneArgs.map{_.get}))))
        else
          None
      }
      case i@IntersectionType(sts) => {
        val (constr, rest) = extract(isConstructor _, sts)
        if(!rest.forall(isLiteral))
          None
        else constr match {
          case None => Some(i)
          case Some(c@ConstructorType(_, _)) => {
            canOneLevel(c) match {
              case Some(IntersectionType(Seq(c))) => Some(IntersectionType(rest :+ c))
              case _ => None
            }
          }
          case _ => error("unexpected")
        }
      }
      case _ => None
    }

    def normalForm(lhs: SetType): SetType = lhs match {
      case EmptyType => lhs
      case IntersectionType(sts) => IntersectionType(sts.map{
        case ConstructorType(n, args) => ConstructorType(n, args.map(normalForm))
        case x => x
      })
      case s => IntersectionType(Seq(s))
    }
    def toOneLevels(lhs: SetType): Set[SetType] = {
      import scala.collection.mutable.ListBuffer
      val newCnstrs = ListBuffer[SetType]()
      def toOneLevel0(lhs: SetType): SetType = lhs match {
        case VariableType(_) => lhs
        case IntersectionType(Seq(s)) => s
        case UnionType(Seq(s)) => s
        case _ => {
          val nv = freshVar("x")
          lhs match {
            case EmptyType => newCnstrs += nv
            case UniversalType => newCnstrs += ComplementType(nv)
            case ComplementType(v@VariableType(_)) => {
              newCnstrs += IntersectionType(Seq(nv, v))
              newCnstrs += IntersectionType(Seq(ComplementType(nv), ComplementType(v)))
            }
            case IntersectionType(sts) => {
              newCnstrs += IntersectionType(ComplementType(nv) +: sts)
              sts.foreach(s => newCnstrs += IntersectionType(Seq(nv, ComplementType(s))))
            }
            case UnionType(sts) => {
              newCnstrs += IntersectionType(nv +: sts.map(s => ComplementType(s)))
              sts.foreach(s => newCnstrs += IntersectionType(Seq(ComplementType(nv), s)))
            }
            case c@ConstructorType(name, args) => {
              newCnstrs += IntersectionType(Seq(ComplementType(nv), c))
              args.zipWithIndex.foreach{
                case (arg, i) => newCnstrs += IntersectionType(Seq(
                  nv, 
                  ConstructorType(name, args.zipWithIndex.map{case (arg, j) => if(i == j) ComplementType(arg) else IntersectionType(Seq())})))
              }
              constructors.foreach{
                case (n, a) => 
                  if(n != name) 
                    newCnstrs += IntersectionType(Seq(nv, ConstructorType(n, (1 to a).map(_ => IntersectionType(Seq())))))
              }
            }
            case _ => error("unexpected")
          }
          nv
        }
      }
      val nlhs = mapPostorder(lhs, toOneLevel0)
      val res = newCnstrs.toSet + nlhs
      res
    }


    val lhsSystem = system.map{
      case Include(s, EmptyType) => s
      case Include(s1, s2) => IntersectionType(Seq(s1, ComplementType(s2)))
    }
    val res = lhsSystem.flatMap(lhs => canOneLevel(lhs) match {
      case Some(s) => Set(s)
      case None => toOneLevels(lhs)
    })
    val normalRes = res.map(normalForm)
    normalRes.map(lhs => Include(lhs, EmptyType))
  }

  def isConstructor(s: SetType): Boolean = s match {
    case ConstructorType(_, _) => true
    case _ => false
  }
  def isLiteral(s: SetType): Boolean = s match {
    case VariableType(_) => true
    case ComplementType(VariableType(_)) => true
    case _ => false
  }
  def isInterLit(s: SetType): Boolean = s match {
    case IntersectionType(sts) => sts.forall(isLiteral)
    case _ => false
  }
  def isOneLevel(s: SetType): Boolean = s match {
    case EmptyType => true
    case IntersectionType(Seq()) => true
    case IntersectionType(sts) => {
      val (init, last) = (sts.init, sts.last)
      if(init.forall(isLiteral)) {
        if(isConstructor(last)) {
          val ConstructorType(_, args) = last 
          args.forall(isInterLit)
        } else if(isLiteral(last)) {
          true
        } else false
      } else false
    }
    case _ => false
  }
  def isOneLevel(r: Relation): Boolean = r match {
    case Include(s1, EmptyType) if isOneLevel(s1) => true
    case _ => {println("not one level: " + r); false}
  }
  def isOneLevel(system: Set[Relation]): Boolean = system.forall(isOneLevel)
  def vars(system: Set[Include]): Set[String] = system.foldLeft(Set[String]())((a, incl) => 
    a ++ Manip.vars(incl))
}
