package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object FunctionClosure extends Pass {

  val description = "Closing function with its scoping variables"

  private var pathConstraints: List[Expr] = Nil
  private var enclosingLets: List[(Identifier, Expr)] = Nil
  private var newFunDefs: Map[FunDef, FunDef] = Map()

  def apply(program: Program): Program = {
    newFunDefs = Map()
    val funDefs = program.definedFunctions
    funDefs.foreach(fd => {
      pathConstraints = fd.precondition.toList
      fd.body = fd.body.map(b => functionClosure(b, fd.args.map(_.id).toSet))
      fd.postcondition = fd.postcondition.map(b => functionClosure(b, fd.args.map(_.id).toSet))
    })
    program
  }

  private def functionClosure(expr: Expr, bindedVars: Set[Identifier]): Expr = expr match {
    case l @ LetDef(fd, rest) => {
      //val bodyVars: Set[Identifier] = variablesOf(fd.body.getOrElse(BooleanLiteral(true))) ++ 
      //                                variablesOf(precondition.getOrElse(BooleanLiteral(true))) ++ 
      //                                variablesOf(postcondition.getOrElse(BooleanLiteral(true)))

      //val capturedVars = bodyVars.intersect(bindedVars)// this should be the variable used that are in the scope
      //val capturedLets = enclosingLets.filter(let => capturedVars.contains(let._1))
      //val (constraints, allCapturedVars) = filterConstraints(capturedVars) //all relevant path constraints
      //val capturedVarsWithConstraints = allCapturedVars.toSeq


      /* let's just take everything for now */
      val capturedVars = bindedVars.toSeq 
      val capturedLets = enclosingLets
      val capturedConstraints = pathConstraints

      val freshIds: Map[Identifier, Identifier] = capturedVars.map(v => (v, FreshIdentifier(v.name).setType(v.getType))).toMap
      val freshVars: Map[Expr, Expr] = freshIds.map(p => (p._1.toVariable, p._2.toVariable))
      
      val extraVarDeclIds = capturedVars.toSet.diff(capturedLets.map(p => p._1).toSet).toSeq
      val extraVarDecls = extraVarDeclIds.map(id =>  VarDecl(freshIds(id), id.getType))
      val newVarDecls = fd.args ++ extraVarDecls
      val newFunId = FreshIdentifier(fd.id.name)
      val newFunDef = new FunDef(newFunId, fd.returnType, newVarDecls).setPosInfo(fd)
      newFunDef.fromLoop = fd.fromLoop
      newFunDef.parent = fd.parent
      newFunDef.addAnnotation(fd.annotations.toSeq:_*)

      val freshPrecondition = fd.precondition.map(expr => replace(freshVars, expr))
      val freshPostcondition = fd.postcondition.map(expr => replace(freshVars, expr))
      val freshBody = fd.body.map(expr => replace(freshVars, expr))
      val freshConstraints = capturedConstraints.map(expr => replace(freshVars, expr))
      val freshLets = capturedLets.map{ case (i, v) => (freshIds(i), replace(freshVars, v)) }

      def substFunInvocInDef(expr: Expr): Option[Expr] = expr match {
        case fi@FunctionInvocation(fd2, args) if fd2.id == fd.id => Some(FunctionInvocation(newFunDef, args ++ extraVarDeclIds.map(_.toVariable)).setPosInfo(fi))
        case _ => None
      }
      val oldPathConstraints = pathConstraints
      val oldEnclosingLets = enclosingLets
      pathConstraints = (fd.precondition.getOrElse(BooleanLiteral(true)) :: pathConstraints).map(e => replace(freshVars, e))
      enclosingLets = enclosingLets.map{ case (i, v) => (freshIds(i), replace(freshVars, v)) }

      val recPrecondition = freshConstraints match {
        case List() => freshPrecondition
        case precs => Some(And(freshPrecondition.getOrElse(BooleanLiteral(true)) +: precs))
      }
      val recBody = freshBody.map(b =>
                      functionClosure(b, bindedVars.map(id => freshIds(id)) ++ newVarDecls.map(_.id))
                    ).map(b => searchAndReplaceDFS(substFunInvocInDef)(b))
      val finalBody = recBody.map(b => freshLets.foldLeft(b){ case (bacc, (i, v)) => Let(i, v, bacc) })

      pathConstraints = oldPathConstraints
      enclosingLets = oldEnclosingLets

      newFunDef.precondition = recPrecondition
      newFunDef.body = finalBody
      newFunDef.postcondition = freshPostcondition

      def substFunInvocInRest(expr: Expr): Option[Expr] = expr match {
        case fi@FunctionInvocation(fd2, args) if fd2.id == fd.id => Some(FunctionInvocation(newFunDef, args ++ extraVarDeclIds.map(_.toVariable)).setPosInfo(fi))
        case _ => None
      }
      val recRest = searchAndReplaceDFS(substFunInvocInRest)(functionClosure(rest, bindedVars))
      LetDef(newFunDef, recRest).setType(l.getType)
    }
    case l @ Let(i,e,b) => {
      val re = functionClosure(e, bindedVars)
      enclosingLets ::= (i, re)
      val rb = functionClosure(b, bindedVars + i)
      enclosingLets = enclosingLets.tail
      Let(i, re, rb).setType(l.getType)
    }
    case i @ IfExpr(cond,then,elze) => {
      val rCond = functionClosure(cond, bindedVars)
      pathConstraints ::= rCond
      val rThen = functionClosure(then, bindedVars)
      pathConstraints = pathConstraints.tail
      pathConstraints ::= Not(rCond)
      val rElze = functionClosure(elze, bindedVars)
      pathConstraints = pathConstraints.tail
      IfExpr(rCond, rThen, rElze).setType(i.getType)
    }
    case n @ NAryOperator(args, recons) => {
      val rargs = args.map(a => functionClosure(a, bindedVars))
      recons(rargs).setType(n.getType)
    }
    case b @ BinaryOperator(t1,t2,recons) => {
      val r1 = functionClosure(t1, bindedVars)
      val r2 = functionClosure(t2, bindedVars)
      recons(r1,r2).setType(b.getType)
    }
    case u @ UnaryOperator(t,recons) => {
      val r = functionClosure(t, bindedVars)
      recons(r).setType(u.getType)
    }
    case m @ MatchExpr(scrut,cses) => { //TODO: will not work if there are actual nested function in cases
      //val rScrut = functionClosure(scrut, bindedVars)
      m
    }
    case t if t.isInstanceOf[Terminal] => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in FunctionClosure: " + unhandled)
  }

  //filter the list of constraints, only keeping those relevant to the set of variables
  def filterConstraints(vars: Set[Identifier]): (List[Expr], Set[Identifier]) = {
    var allVars = vars
    var newVars: Set[Identifier] = Set()
    var constraints = pathConstraints
    var filteredConstraints: List[Expr] = Nil
    do {
      allVars ++= newVars
      newVars = Set()
      constraints = pathConstraints.filterNot(filteredConstraints.contains(_))
      constraints.foreach(expr => {
        val vs = variablesOf(expr)
        if(!vs.intersect(allVars).isEmpty) {
          filteredConstraints ::= expr
          newVars ++= vs.diff(allVars)
        }
      })
    } while(newVars != Set())
    (filteredConstraints, allVars)
  }

}
