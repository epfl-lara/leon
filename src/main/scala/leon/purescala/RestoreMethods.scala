/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import Common._
import Expressions._
import ExprOps.{replaceFromIDs,functionCallsOf}
import DefOps.{applyOnFunDef,preMapOnFunDef}
import Types._
import utils.GraphOps._

object RestoreMethods extends TransformationPhase {
  
  val name = "Restore methods"
  val description = "Restore methods that were previously turned into standalone functions"
    
  /**
   * New functions are returned, whereas classes are mutated
   */
  def apply(ctx : LeonContext, p : Program) = {
        
    var fd2Md = Map[FunDef, FunDef]()
    var whoseMethods = Map[ClassDef, Seq[FunDef]]()
    
    for ( (Some(cd : ClassDef), funDefs) <- p.definedFunctions.groupBy(_.origOwner).toSeq ) {
      whoseMethods += cd -> funDefs
      for (fn <- funDefs) {
        val theName = try {
          // Remove class name from function name, if it is there
          val maybeClassName = fn.id.name.substring(0,cd.id.name.length)
        
          if (maybeClassName == cd.id.name) {
            fn.id.name.substring(cd.id.name.length + 1) // +1 to also remove $
          } else {
            fn.id.name
          }
        } catch {
          case e : IndexOutOfBoundsException => fn.id.name
        }
        val md = new FunDef(
          id = FreshIdentifier(theName), 
          tparams = fn.tparams diff cd.tparams,
          params = fn.params.tail, // no this$
          returnType = fn.returnType,
          defType = fn.defType
        ).copiedFrom(fn)
        md.copyContentFrom(fn)

        // first parameter should become "this"
        val thisType = fn.params.head.getType.asInstanceOf[ClassType]
        val theMap = Map(fn.params.head.id -> This(thisType))
        val mdFinal = applyOnFunDef(replaceFromIDs(theMap, _))(md)
        
        fd2Md += fn -> mdFinal       
      }
    } 
     
    /**
     * Substitute a function in an expression with the respective new method
     */
    def substituteMethods = preMapOnFunDef ({
      case FunctionInvocation(tfd,args) if fd2Md contains tfd.fd => {
        val md = fd2Md.get(tfd.fd).get // the method we are substituting
        val mi = MethodInvocation(
          args.head, // "this"
          args.head.getType.asInstanceOf[ClassType].classDef, // this.type
          md.typed(tfd.tps.takeRight(md.tparams.length)),  // throw away class type parameters
          args.tail // rest of the arguments
        )
        Some(mi)
      }
      case _ => None
    }, true) _
    
    /**
     * Renew that function map by applying subsituteMethods on its values to obtain correct functions
     */
    val fd2MdFinal = fd2Md.mapValues(substituteMethods)
    val oldFuns = fd2MdFinal.map{ _._1 }.toSet
    
    // We need a special type of transitive closure, detecting only trans. calls on the same argument
    def transCallsOnSameArg(fd : FunDef) : Set[FunDef] = {
      require(fd.params.length == 1)
      require(fd.params.head.getType.isInstanceOf[ClassType])
      def callsOnSameArg(fd : FunDef) : Set[FunDef] = {
        val theArg = fd.params.head.toVariable
        functionCallsOf(fd.fullBody) collect { case fi if fi.args contains theArg => fi.tfd.fd } 
      }
      reachable(callsOnSameArg,fd)
    }
    
    def refreshModule(m : ModuleDef) = {
      val newFuns : Seq[FunDef] = m.definedFunctions diff fd2MdFinal.keys.toSeq map substituteMethods// only keep non-methods
      for (cl <- m.definedClasses) {
        // We're going through some hoops to ensure strict fields are defined in topological order
        
        // We need to work with the functions of the original program to have access to CallGraph
        val (strict, other) = whoseMethods.getOrElse(cl,Seq()).partition{ fd2MdFinal(_).canBeStrictField }
        val strictSet = strict.toSet
        // Make the call-subgraph that only includes the strict fields of this class 
        val strictCallGraph = strict.map { st => 
          (st, transCallsOnSameArg(st) & strictSet)
        }.toMap
        // Topologically sort, or warn in case of cycle
        val strictOrdered = topologicalSorting(strictCallGraph) fold (
          cycle => {
            ctx.reporter.warning(
              s"""|Fields
                  |${cycle map {_.id} mkString "\n"} 
                  |are involved in circular definition!""".stripMargin
            )
            strict
          },
          r => r
        )
  
        for (fun <- strictOrdered ++ other) { 
          cl.registerMethod(fd2MdFinal(fun)) 
        }
      }
      m.copy(defs = m.definedClasses ++ newFuns).copiedFrom(m)    
    }

    val modsToMods = ( for { u <- p.units; m <- u.modules } yield (m,refreshModule(m)) ).toMap
    
    p.copy(units = p.units map { u => u.copy(
      modules = u.modules map modsToMods,
      imports = u.imports flatMap {
        // Don't include imports for functions that became methods
        case SingleImport(fd : FunDef) if oldFuns contains fd => None
        case SingleImport(m : ModuleDef) => Some(SingleImport(modsToMods(m)))
        case WildcardImport(m : ModuleDef) => Some(WildcardImport(modsToMods(m)))
        case other => Some(other)
      }
    )})
      
    
  }

}
