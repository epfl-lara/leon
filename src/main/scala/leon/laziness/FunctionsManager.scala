package leon
package laziness

import invariant.util._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import HOMemUtil._
import ProgramUtil._
import invariant.datastructure._
import purescala.Types._

class FunctionsManager(p: Program) {

  val debug = false
  implicit val prog = p
  /**
   * The call-graph includes only static calls. Indirect calls are anyway treated conservatively based on their types.
   * The graph includes calls made through the specs.
   * TODO: for now call-graphs do not contain field invocations. We need to update this!
   */
  sealed abstract class Label // these are labels of the call-graph edges
  case class Specs() extends Label
  case class Star() extends Label
  case class WithState() extends Label
  case class Lamb() extends Label
  case class LambWoPre() extends Label
  case class NoLabel() extends Label

  val cg = {
    val dg = new DirectedLabeledGraph[FunDef, Label] with CallGraph {} // the labels denote whether a call is made through `star` or not
    p.definedFunctions.foreach { fd =>
      dg.addNode(fd)
      fd.fullBody match {
        case NoTree(_) =>
        case body =>
          def rec(l: Label)(e: Expr): Unit = e match {
            // ignore non-real calls. It following cases, calls are used as a way to refer to closures.
            case f: FunctionInvocation if isIsFun(f) =>
            case cc: CaseClass if isFunCons(cc)      =>
            // other calls may be tagged by labels
            case cc @ CaseClass(_, args) if isWithStateCons(cc) =>
              args map rec(WithState())
            case f @ FunctionInvocation(_, Seq(CaseClass(_, Seq(invExpr)))) if isStarInvocation(f) =>
              rec(Star())(invExpr)
            case f @ FunctionInvocation(TypedFunDef(callee, _), args) => //if !callee.canBeStrictField
              dg.addEdge(fd, callee, l)
              args map rec(l)
            case Ensuring(e, Lambda(_, post)) =>
              rec(l)(e)
              rec(Specs())(post)
            case Require(pre, e) =>
              rec(Specs())(pre)
              rec(l)(e)
            case Lambda(_, body) =>
              body match {
                case FunctionInvocation(tfd, _) if tfd.fd.hasPrecondition =>
                  rec(Lamb())(body)
                case FunctionInvocation(tfd, _) =>
                  rec(LambWoPre())(body)
                case _ =>
                  rec(LambWoPre())(body)
              }
            case Operator(args, _) => args map rec(l)
          }
          rec(NoLabel())(body)
      }
    }
    dg
  }

  /**
   * all lambdas in the program.
   * Note: function specifications cannot create lambdas.
   */
  val lambdasList = userLevelFunctions(p).flatMap {
    case fd if fd.hasBody =>
      def rec(e: Expr): Seq[Lambda] = e match {
        case finv: FunctionInvocation if isIsFun(finv) => Seq() //skip
        case finv: FunctionInvocation if isFunMatch(finv) => Seq() //skip
        case l: Lambda => Seq(l)
        case Operator(args, _) => args flatMap rec
      }
      rec(fd.body.get)
    case _ => Seq[Lambda]()
  }.distinct

  val paramFunTypes = (userLevelFunctions(p) ++ userLevelClasses(p)).flatMap { d =>
    val params = d match {
      case cd: ClassDef => cd.fields
      case fd: FunDef   => fd.params
    }
    params.collect {
      case vd if vd.getType.isInstanceOf[FunctionType] => vd.getType.asInstanceOf[FunctionType]
    }
  }.distinct

  val funTypesInProgram = (paramFunTypes ++ lambdasList.map(_.getType.asInstanceOf[FunctionType])).distinct

  val memoFuns = p.definedFunctions.collect {
    case fd if fd.hasBody && isMemoized(fd) => fd
  }.distinct

  if (debug) {
    println("Function types passed as parameters: \n" + paramFunTypes.mkString("\n"))
    println("Lambda terms found: \n" + lambdasList.mkString("\n"))
    println("Memoized fundefs found: \n" + memoFuns.map(_.id).mkString("\n"))

  }
  /*
   * Lambdas need not be a part of read roots, because its body needs state, the function creating lambda will be
   * marked as needing state.
   * TODO: Only those applications that may call a memoized function  should be valroots
   */
  val (funsNeedStates, funsRetStates, funsNeedStateTps) = {
    var needTargsRoots = Set[FunDef]()
    var readRoots = Set[FunDef]()
    var updateRoots = Set[FunDef]()
    userLevelFunctions(p).foreach { fd =>
      if (fd.params.exists(vd => isFunSetType(vd.getType))) // functions that use `stateType` args need `stateParams`
        needTargsRoots += fd
      fd.fullBody match {
        case NoTree(_) =>
        case _ =>
          def rec(e: Expr)(implicit inspec: Boolean): Unit = e match {
            // skip recursing into the following functions
            case f: FunctionInvocation if isIsFun(f)            =>
            case cc: CaseClass if isFunCons(cc)                 =>
            case cc @ CaseClass(_, args) if isWithStateCons(cc) =>
            case finv @ FunctionInvocation(_, Seq(CaseClass(_, Seq(invExpr)))) if isStarInvocation(finv) =>
              needTargsRoots += fd
              invExpr match {
                case Application(l, args) => // we need to prevent the application here from being treated as a `read/write` root
                  (l +: args) foreach rec
                case FunctionInvocation(_, args) =>
                  args foreach rec
              }
            case finv @ FunctionInvocation(_, args) if cachedInvocation(finv) =>
              readRoots += fd
              args foreach rec
            case Application(l, args) if !inspec => // note: not all applications need to update state but is hard to determine this upfront
              updateRoots += fd
              readRoots += fd
              (l +: args) foreach rec
            case FunctionInvocation(tfd, args) if !inspec && isMemoized(tfd.fd) =>
              updateRoots += fd
              readRoots += fd
              args foreach rec
            case Operator(args, _) =>
              args foreach rec
          }
          if (fd.hasBody)
            rec(fd.body.get)(false)
          if (fd.hasPrecondition)
            rec(fd.precondition.get)(true)
          if (fd.hasPostcondition)
            rec(fd.postcondition.get)(true)
      }
    }
    //println("Original sucessors of concrete: "+cg.succsWithLabels(node).map{ case (fd, lbs) => fd.id +" label: "+lbs.mkString(",")}.mkString("\n"))
    // `updateCallers` are all functions that transitively call `updateRoots` only through edges labeled `None`
    val updatefuns = cg.projectOnLabel(NoLabel()).reverse.BFSReachables(updateRoots.toSeq)
    // `readfuns` are all functions that transitively call `readRoots` not through edges labeled `withState` or `Star`
    val readfuns = cg.removeEdgesWithLabels(Set(WithState(), Star(), LambWoPre())).reverse.BFSReachables(readRoots.toSeq)
    // all functions that call `star` no matter what
    val needTargsCallers = cg.transitiveCallers(needTargsRoots.toSeq)
    //println("Ret roots: " + updateRoots.map(_.id) + " ret funs: " + updatefuns.map(_.id))
    //println("Read roots: " + readRoots.map(_.id) + " read funs: " + readfuns.map(_.id))
    //println("NeedTArgs roots: " + needTargsRoots.map(_.id) + " NeedTArgs funs: " + needTargsCallers.map(_.id))
    (readfuns ++ updatefuns, updatefuns, needTargsCallers ++ readfuns ++ updatefuns)
  }

  lazy val callersnTargetOfLambdas = {
    var consRoots = Set[FunDef]()
    funsNeedStates.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case l: Lambda =>
            consRoots += fd
          case _ =>
        }(fd.body.get)
      case _ => ;
    }
    cg.transitiveCallers(consRoots.toSeq) //++ targets
  }

  lazy val cgWithoutSpecs = CallGraphUtil.constructCallGraph(p, true, false)
  lazy val callersOfCached = {
    var roots = Set[FunDef]()
    funsNeedStates.foreach {
      case fd if fd.hasBody =>
        postTraversal {
          case finv: FunctionInvocation if cachedInvocation(finv) =>
            roots += fd
          case _ =>
            ;
        }(fd.body.get)
      case _ => ;
    }
    cgWithoutSpecs.transitiveCallers(roots.toSeq)
  }

  def hasStateIndependentBehavior(fd: FunDef): Boolean = {
    // every function that does not call isEvaluated or is Susp has a state independent behavior
    !callersOfCached.contains(fd)
  }
}
