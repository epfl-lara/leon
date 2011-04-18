package purescala.isabelle

import purescala.Reporter
import purescala.Trees._
import purescala.Definitions._
import purescala.Extensions._
import purescala.Settings._
import purescala.Common.Identifier
import purescala.TypeTrees._
   
import java.lang.StringBuffer
import java.io._
import scala.collection.mutable.ListMap

class Main(reporter : Reporter) extends Analyser(reporter) {
  val description = "Generates Isabelle source"
  override val shortDescription = "isabelle"
	var mapParentTypes = new ListMap[String,String]

	//map for each function keeps the functions that it calls inside it 
	var functionDependsOn = new ListMap[String, List[String]]
	var currentFunction = ""

	//current #res:
	var current_res = "" 

	//list of binders : for expressions like x match { case binder@expr => E[binder] }
	var bindersMap = new ListMap[MatchCase, (Identifier, String)]


  def apply(tree: Expr): String = {
    val retSB = pp(tree, new StringBuffer, 0)
    retSB.toString
  }

  def apply(tpe: TypeTree): String = {
    val retSB = pp(tpe, new StringBuffer, 0)
    retSB.toString
  }

  def apply(defn: Definition): String = {
    val retSB = pp(defn, new StringBuffer, 0)
    retSB.toString
  }

  private def ind(sb: StringBuffer, lvl: Int) : StringBuffer = {
      sb.append("  " * lvl)
      sb
  }

  // EXPRESSIONS
  // all expressions are printed in-line
  private def ppUnary(sb: StringBuffer, expr: Expr, op1: String, op2: String, lvl: Int): StringBuffer = {
    var nsb: StringBuffer = sb
    nsb.append(op1)
    nsb = pp(expr, nsb, lvl)
    nsb.append(op2)
    nsb
  }

  private def ppBinary(sb: StringBuffer, left: Expr, right: Expr, op: String, lvl: Int): StringBuffer = {
    var nsb: StringBuffer = sb
    nsb.append("(")
    nsb = pp(left, nsb, lvl)
    nsb.append(op)
    nsb = pp(right, nsb, lvl)
    nsb.append(")")
    nsb
  }

  private def ppNary(sb: StringBuffer, exprs: Seq[Expr], pre: String, op: String, post: String, lvl: Int): StringBuffer = {
    var nsb = sb
    nsb.append(pre)
    val sz = exprs.size
    var c = 0

    exprs.foreach(ex => {
      nsb = pp(ex, nsb, lvl) ; c += 1 ; if(c < sz) nsb.append(op)
    })

    nsb.append(post)
    nsb
  }

  private def pp(tree: Expr, sb: StringBuffer, lvl: Int): StringBuffer = tree match {
    case Variable(id) => {
				//we need to replace binders by their actual expressions
				var found = false
				bindersMap.foreach( t =>
					if(t._2._1.toString.compareTo(id.toString) == 0){
						found = true
						sb.append(t._2._2) 
					}
				)
				if(!found)
					sb.append("var_" + id + "_var") //add this to avoid isabelle reserved names like "min"
				sb
		}
    case Let(b,d,e) => {
				var nsb = pp(d, sb.append("(let var_" + b + "_var = "), lvl).append(" in \n")
				ind(nsb , lvl + 2)			
        pp(e,nsb, lvl + 2).append(")")
    }
    case And(exprs) => ppNary(sb, exprs, "(", " \\<and> ", ")", lvl)   
    case Or(exprs) => ppNary(sb, exprs, "(", " \\<or> ", ")", lvl)  
    case Not(Equals(l, r)) => ppBinary(sb, l, r, " \\<noteq> ", lvl)    
    case Iff(l,r) => ppBinary(sb, l, r, " \\<Leftrightarrow> ", lvl)              
    case Implies(l,r) => ppBinary(sb, l, r, " \\<longrightarrow> ", lvl)              
    case UMinus(expr) => ppUnary(sb, expr, "-(", ")", lvl)
    case Equals(l,r) => ppBinary(sb, l, r, " = ", lvl)
    case IntLiteral(v) => sb.append(v)
    case BooleanLiteral(v) => v match{
			case true =>	sb.append("True")
			case false => sb.append("False")
		}
    case StringLiteral(s) => sb.append("\"" + s + "\"")

    case CaseClass(cd, args) => { 
      var nsb = sb
      nsb.append("(" + cd.id)
      nsb = ppNary(nsb, args, " ", " ", ")", lvl)
      nsb
    }
    case CaseClassInstanceOf(cd, e) => {
			reporter.error("[not translated in isabelle] instanceOf ")
      var nsb = sb
      nsb = pp(e, nsb, lvl)
      nsb.append(".isInstanceOf[" + cd.id + "]")
      nsb
    }

    case CaseClassSelector(ccdef, cc, id) => {
			sb.append("(" + ccdef.id + "__" + id + " ")
			pp(cc,sb,0)
			sb.append(")")
		}

//does it calls a previous defined function or not ?
    case FunctionInvocation(fd, args) => {
      var nsb = sb
			if(currentFunction.compareTo("") != 0 && currentFunction.compareTo(fd.id.toString)!= 0){
				var list = Nil : List[String]
				functionDependsOn.get(currentFunction)	match {
		     				case None => reporter.error("function not defined: " + currentFunction)
		     				case Some(l) => list = l
		    }
				list = fd.id.toString :: list
				functionDependsOn.update(currentFunction, list.distinct)				
			}
      nsb.append("(" + fd.id)
      nsb = ppNary(nsb, args, " ", " ", " ", lvl)
      nsb.append(")")
			nsb
    }
    case Plus(l,r) => ppBinary(sb, l, r, " + ", lvl)
    case Minus(l,r) => ppBinary(sb, l, r, " - ", lvl)
    case Times(l,r) => ppBinary(sb, l, r, " * ", lvl)
    case Division(l,r) => ppBinary(sb, l, r, " / ", lvl)
    case LessThan(l,r) => ppBinary(sb, l, r, " < ", lvl)
    case GreaterThan(l,r) => ppBinary(sb, l, r, " > ", lvl)
    case LessEquals(l,r) => ppBinary(sb, l, r, " \\<le> ", lvl)      // \leq
    case GreaterEquals(l,r) => ppBinary(sb, l, r, " \\<ge> ", lvl)   // \geq
    case FiniteSet(rs) => ppNary(sb, rs, "{", ", ", "}", lvl) 
    case FiniteMultiset(rs) => {
			reporter.error("[not handled ] FinitMultiset")
			ppNary(sb, rs, "{|", ", ", "|}", lvl) //TODO
		}
    case EmptySet(_) => sb.append("{}")                          // Ø
    case EmptyMultiset(_) => sb.append("{}")                     // Ø
    case Not(ElementOfSet(s,e)) => ppBinary(sb, s, e, " \\<notin> ", lvl) // \notin
    case ElementOfSet(s,e) => ppBinary(sb, s, e, " \\<in> ", lvl)    // \in
    case SubsetOf(l,r) => ppBinary(sb, l, r, " \\<subseteq> ", lvl)        // \subseteq
    case Not(SubsetOf(l,r)) => ppBinary(sb, l, r, " \\<not> \\<subseteq> ", lvl)        // \notsubseteq
    case SetMin(s) => {
			reporter.error("[not handled ] SetMin")
			pp(s, sb, lvl).append(".min") //TODO
		}
    case SetMax(s) => {
			reporter.error("[not handled ] SetMax")
			pp(s, sb, lvl).append(".max") //TODO
		}
    case SetUnion(l,r) => ppBinary(sb, l, r, " \\<union> ", lvl)        // \cup
    case MultisetUnion(l,r) => ppBinary(sb, l, r, " \\<union> ", lvl)   // \cup
    case SetDifference(l,r) => ppBinary(sb, l, r, " - ", lvl)       
    case MultisetDifference(l,r) => ppBinary(sb, l, r, " - ", lvl)       
    case SetIntersection(l,r) => ppBinary(sb, l, r, " \\<inter> ", lvl) // \cap
    case MultisetIntersection(l,r) => ppBinary(sb, l, r, " \\<inter> ", lvl) // \cap
    case SetCardinality(t) => ppUnary(sb, t, "(card ", ")", lvl) 
    case MultisetCardinality(t) => ppUnary(sb, t, "(card ", ")", lvl)
    case MultisetPlus(l,r) => {
			reporter.error("[not handled ] MultiSetPlus")
			ppBinary(sb, l, r, " \u228E ", lvl)    // TODO
		}
    case MultisetToSet(e) => { 
			reporter.error("[not handled ] MultisetToSet")
			pp(e, sb, lvl).append(".toSet") //TODO
    }
    case IfExpr(c, t, e) => {
      var nsb = sb
      nsb.append("(if (")
      nsb = pp(c, nsb, lvl)
      nsb.append(") then (\n")
      ind(nsb, lvl+1)
      nsb = pp(t, nsb, lvl+1)
      nsb.append("\n")
      ind(nsb, lvl + 1)
      nsb.append(") else (\n")
      ind(nsb, lvl+1)
      nsb = pp(e, nsb, lvl+1)
      nsb.append("\n")
      ind(nsb, lvl )
      nsb.append("))")
      nsb
    }

    case SimplePatternMatching(e, ct, patterns) => {
      // e is the expression being matched
      // ct is the ClassType of the expression
      
      for((ccd, id, ids, ex) <- patterns) {
        // describes a pattern of the form: id @ CCD(ids) => ex
        ...
      }

      throw Exception("unsupported")
    }

    case mex @ MatchExpr(s, csc) => {
      def ppc(sb: StringBuffer, p: Pattern, matchcase : MatchCase): StringBuffer = p match {
        
				case CaseClassPattern(bndr, ccd, subps) => {
          var buf = new StringBuffer
          buf.append("(").append(ccd.id).append(" ")
          var c = 0
          val sz = subps.size
          subps.foreach(sp => {
            buf = ppc(buf, sp, matchcase)
            if(c < sz - 1)
              buf.append(" ")
            c = c + 1
          })
          buf.append(")")
					
          bndr.foreach(b => bindersMap.update(matchcase, (b, buf.toString)))

					sb.append(buf.toString)
        }
        case WildcardPattern(None)     => sb.append("_")
        case WildcardPattern(Some(id)) => {
					sb.append("var_" + id.toString + "_var")
				}
        case _ => sb.append("Pattern?")
      }

      var nsb = sb
      nsb.append("(case ")
      nsb == pp(s, nsb, lvl)
			nsb.append(" of\n")

			var len1 = csc.size
			var c1 = 0

      csc.foreach(cs => {
        ind(nsb, lvl+2)
        nsb = ppc(nsb, cs.pattern , cs)

       nsb.append(" \\<Rightarrow> \n")
				ind(nsb, lvl + 4)

        cs.theGuard.foreach(g => {
//          nsb.append(" if ")
//          nsb = pp(g, nsb, lvl+1)
						reporter.error("match case has IF condition - not handled!")
        })
 
        nsb = pp(cs.rhs, nsb, lvl+ 4)
				if(c1 < len1  - 1)
        	nsb.append(" |")
				nsb.append("\n")
				c1 = c1 + 1

				bindersMap = bindersMap - cs
      })
      ind(nsb, lvl).append(" )\n")
      nsb
    }

		//#res
    case ResultVariable() => sb.append(current_res) 
    case Not(expr) => ppUnary(sb, expr, "\\<not>(", ")", lvl)  

    case e @ Error(desc) => {
      var nsb = sb
      nsb.append("error(\"" + desc + "\")[")
      nsb = pp(e.getType, nsb, lvl)
      nsb.append("]")
      nsb
    }

    case _ => sb.append("Expr?")
  }

  // TYPE TREES
  // all type trees are printed in-line
  private def pp(tpe: TypeTree, sb: StringBuffer, lvl: Int): StringBuffer = tpe match {
    case Untyped => sb.append("???")
    case Int32Type => sb.append("int")
    case BooleanType => sb.append("bool")
    case SetType(bt) => pp(bt, sb.append("("), lvl).append(" set)")
    case MultisetType(bt) => {
			println("[not handled] multisettype")
			pp(bt, sb.append("Multiset["), lvl).append("]")
		}
    case c: ClassType => sb.append(mapParentTypes.get(c.classDef.id.toString) match {
			case None => c.classDef.id
			case Some(l) => l
			}
		)
    case _ => sb.append("Type?")
  }

  // DEFINITIONS
  // all definitions are printed with an end-of-line
  private def pp(defn: Definition, sb: StringBuffer, lvl: Int): StringBuffer = {

    defn match {
      case Program(id, mainObj) => {
        assert(lvl == 0)
        pp(mainObj, sb, lvl)

//				println("function depends on :\n")
//				println(functionDependsOn)
  
				sb.append("end\n")
    }

      case ObjectDef(id, defs, invs) => {
        var nsb = sb
        sb.append("theory " + id + "\n")
        sb.append("imports Datatype Main\n")
        sb.append("begin\n\n")

        val definedFunctions : Seq[FunDef] = defs.filter(_.isInstanceOf[FunDef]).map(_.asInstanceOf[FunDef])
        val definedClasses : Seq[ClassTypeDef] = defs.filter(_.isInstanceOf[ClassTypeDef]).map(_.asInstanceOf[ClassTypeDef])

       /*interpret datatype definitions:
         case class Binary(exp1 : Expr, op : BinOp, exp2 : Expr) extends Expr  ==>
         datatype Expr = ...
        			   | Binary Expr BinOp Expr        
				*/
        var map = new ListMap[String, List[List[String]]]

        definedClasses.foreach(dc => {
          dc match{
		      case AbstractClassDef(id2, parent) => {
		        parent match {
		        	case None => 
		        	case _ => reporter.error("[not analyzed] sealed class " + id2 + " should not have a parent")
		        }
		      }
		       //suppose parent is not a typed class (e.g "List int")
		      case CaseClassDef(id2, parent, varDecls) => {
		     		var datatype : Option[List[List[String]]] = None
		        var nsb = sb
		        parent match{
		     		case None => reporter.error("case class without parent")
		     		case Some(AbstractClassDef(idparent, ll)) => {
		     			datatype = map.get(idparent.toString)
		     			//list = list of current subtypes of this datatype		     			
		     			var list : List[List[String]] = List()
		     			datatype match {
		     				case None => 
		     				case Some(l) => list = l
		     			}
							
							/*list of the subtype (e.g case Value(v:int) extends Expr  ----> List(Value, int)  ) */
							var subtype_list = Nil : List[String]
		     			subtype_list = subtype_list :+ id2.toString
				
				        varDecls.foreach(vd => {
		     					var subtype = new StringBuffer
				        	pp(vd.tpe, subtype , 0) // type of parameters 
				        	subtype_list = subtype_list :+ subtype.toString
				        })
		     			list = list :+ subtype_list
		     			map.update(idparent.toString, list)
		     		}
		     	}
		      }	  		        	  
          }  
        })      
       
				/*map that keeps every case class in map with its parent */
				/*case class Value (v : Int) extends Whatever  ---> Value will have as parent type Whatever */
				map foreach ( (t1) =>
					for( t2 <- t1._2)
						mapParentTypes.update(t2.head ,t1._1 )
				)

				/* if a case class appears in one definition, then replace it by it parent class`  */
				map foreach( (one_type) => {
					var l = Nil : List[List[String]]
					for(subtype_list <- one_type._2){
						var ll = List(subtype_list.head)
						for(dependent_type <- subtype_list.tail){
							var x = mapParentTypes.get(dependent_type)
							x match {
								case Some(s) => ll = ll :+ s 
								case None => ll = ll :+ dependent_type
							}
						}
						l = l :+ ll
					}
					map.update(one_type._1 , l)
				})

			//	def contains(t: (String, List[List[String]]) ,l : List[(String, List[List[String]])]) : Boolean ={
				def contains(t: (String, Any) ,l : List[(String, Any)]) : Boolean ={
					for(el <- l)
						if (t._1.compareTo(el._1) == 0 )
							return true
					false
				}
        
				/* sort the list of all types such that if one depends on another, then the later is defined first */
				var sortedList = Nil : List[(String, List[List[String]])]
				while(sortedList.size < map.size){
					map foreach((t1) =>
						if(!contains(t1, sortedList)){
							var b = true
							map foreach( (t2) =>
								if(!contains(t2, sortedList) && t1._1.compareTo(t2._1) != 0)
		  	  	    	for(el <- t1._2)
										for(str <- el)
 	 		  	  	  			if(str.compareTo(t2._1) == 0)
    		  	  					b = false
							)
							if(b)
								sortedList = sortedList ::: List(t1)
						}
					)
				}
 
				def preetyPrint (l : List[String], nsb: StringBuffer): Unit ={
					for(el <- l)
						nsb.append(el + " ")
				}

				var type_decl = "datatype "
        sortedList.foreach(p => {
        	p match {
        		case (parenttype, list) => {
        			var numberTabs = (type_decl + parenttype + " ").size
		        	nsb.append(type_decl + parenttype + " = ")
							type_decl = "and "
							preetyPrint(list.head, nsb)
		        	nsb.append("\n")
		        	for (el <- list.tail){
		        		nsb.append(" " * numberTabs)
		        		nsb.append("| ")
								preetyPrint(el,nsb)
								nsb.append("\n")
		        	}
        		}
        	}
        })
        nsb.append("\n")

//================================= functions for field access: ==========================================
/* case class Acc(checking : Int, savings : Int) extends AccLike ----> 
	fun Acc__checking :: "AccLike \<Rightarrow> Int" where
		"Acc__checking var = 
				(case var of (Acc var_checking_var var_savings_var)  \Rightarrow var_checking_var)"
*/
        definedClasses.foreach(dc => {
          dc match{
		      case AbstractClassDef(id2, parent) => 
		       //suppose parent is not a typed class (e.g "List int")
		      case CaseClassDef(id2, parent, varDecls) => {
		        parent match{
		     		case None => reporter.error("case class without parent")
		     		case Some(AbstractClassDef(idparent, ll)) => {
				        varDecls.foreach(vd => {
		     					var subtype = new StringBuffer
				        	pp(vd.tpe, subtype , 0) // type of parameter
									
          				ind(nsb, lvl)
									nsb.append("fun " + id2 + "__" + vd.id + " :: \"" + idparent + " \\<Rightarrow> "+ subtype.toString + "\"")
									nsb.append(" where\n")
									ind(nsb,lvl + 2)
									nsb.append("\"" + id2 + "__" + vd.id + " var = \n")									
									ind(nsb, lvl + 4)
									nsb.append("(case var of (" + id2 )
									for(j <- varDecls)
										nsb.append(" var_" + j.id + "_var")
									nsb.append(") \\<Rightarrow> var_" + vd.id + "_var)\"\n\n")

				        })
		     		}
						case Some(_) => reporter.error("case class has parent another case class - n/a")
		     	}
		      }	  		        	  
          }  
        })      
 
 				//=========================== FUNCTIONS ================       
       //the following sets the right order of functions according to dependencies
        //interpret functions
				var functionCode = new ListMap[String, StringBuffer]

        definedFunctions.foreach(df => {
					var sbaux = new StringBuffer
          sbaux = pp(df, sbaux, lvl)
					sbaux.append("\n\n")

					functionCode.update(df.id.toString, sbaux)
        })
 
	//var functionCode = new ListMap[String, StringBuffer]
	//var functionDependsOn = new ListMap[String, List[String]]
      
				/* sort the list of all types such that if one depends on another, then the later is defined first */
				var sortedFunctionList = Nil : List[String]
				while(sortedFunctionList.size < functionCode.size){
					functionCode foreach((t1) =>
						if(!(sortedFunctionList contains t1._1)){
							var b = true
							var ll = functionDependsOn.get(t1._1) match {
								case Some(lll) => lll
								case None => Nil : List[String]
							}
							functionCode foreach( (t2) =>
								if(!(sortedFunctionList contains t2._1) && t1._1.compareTo(t2._1) != 0){
		  	  	    	for(str <- ll)
 	 		  	  	  		if(str.compareTo(t2._1) == 0)
    		  	  				b = false
								}
							)
							if(b)
								sortedFunctionList = sortedFunctionList ::: List(t1._1)
						}
					)
				}
 
	
				sortedFunctionList foreach ( p =>
					nsb.append(functionCode.get(p) match {
						case Some(buf) => buf.toString
						case None => "fatal error in functions translation"
					})
				) 

				nsb
      }

//========================================== FUNCTIONS =====================================================
  		/*
			def evalOp(v1 : Value, op : BinOp, v2 : Value) : Value = .....
			fun evalOp :: "Value  \<Rightarrow> BinOp \<Rightarrow> Value \<Rightarrow> Value" where
				"evalOp v1 op v2 = ( ..... )"
			*/
 
      //functions : 
      case fd @ FunDef(id, rt, args, body, pre, post) => {
        var nsb = sb
				functionDependsOn.update(id.toString, List())
				currentFunction = id.toString

        for(a <- fd.annotations) {
          ind(nsb, lvl)
          nsb.append("(* @" + a + " *)\n")
        }

        pre.foreach(prec => {
          ind(nsb, lvl)
          nsb.append("(* @pre : ")
          nsb = pp(prec, nsb, lvl)
          nsb.append(" *)\n")
        })

        ind(nsb, lvl)
				if(args.size > 0)
	        nsb.append("fun ")
				else
					nsb.append("definition ")
        nsb.append(id)
        nsb.append(" :: \"")

        val sz = args.size
        var c = 0

       args.foreach(arg => {
          nsb = pp(arg.tpe, nsb, lvl)

          if(c < sz - 1) {
            nsb.append(" \\<Rightarrow> ")
          }
          c = c + 1
        })

				if(args.size > 0)
	        nsb.append(" \\<Rightarrow> ")
        nsb = pp(rt, nsb, lvl)
        nsb.append("\" where \n")

        ind(nsb, lvl)
				nsb.append(" \"")
        nsb.append(id + " ")

        args.foreach(arg => {
          nsb.append("var_" + arg.id + "_var")
          nsb.append(" ")
        })
				
				nsb.append("= \n")
				
        ind(nsb, lvl + 2)
				nsb.append(" ")
        if(body.isDefined)
          pp(body.get, nsb, lvl + 2)
        else
          reporter.error("[unknown function implementation]")

        ind(nsb, lvl)
				nsb.append(" \"\n")

				//@postconditions viewed as lemmas; preconditions are integrated in the lemma statement
				//annotations should help to prove the lemma
			//// TODO : add quantifiers to lemma statement
        post.foreach(postc => {
					nsb.append("\n")
          ind(nsb, lvl)
          nsb.append("lemma " + id + "_postcondition [simp]: shows \"")

					
					if(pre.size > 0){
						var l11 = pre.size
						var c2 = 0		
						nsb.append("(")				
		        pre.foreach(prec => {
  	    	    nsb = pp(prec, nsb, lvl)
							if(c2 < l11 - 1)
								nsb.append(" \\<and> ")
							c2 = c2 + 1
    	    	})
						nsb.append(") \\<longrightarrow> ")
					}

					current_res = "(" + id + " "
	        args.foreach(arg => {
  	        current_res = current_res + "var_" + arg.id + "_var "
      	  })
					current_res = current_res + ")"

          nsb = pp(postc, nsb, lvl)
          nsb.append("\"\n")
					ind(nsb, lvl)

	/*				body.get match {		
				    case mex @ MatchExpr(s, csc) => {
							var strbuf = new StringBuffer
							pp(s, strbuf ,0)
							nsb.append("apply(case_tac " + strbuf.toString + ")\n") 
							ind(nsb,lvl)
						}
						case _ =>
					}

					//apply induction on first argument
	        for(a <- fd.annotations) 
 						if(a.compareTo("induct") == 0 ){
 							nsb.append("apply(induct_tac " + args.head.id + ")\n") 
							ind(nsb,lvl)
						}
*/
					if(args.size > 0){
 							nsb.append("apply(induct_tac var_" + args.head.id + "_var)\n") 
							ind(nsb,lvl)
					}
											
					nsb.append("apply(auto)\n") 
					ind(nsb,lvl)
					nsb.append("done\n") 
					ind(nsb,lvl)
					
        })
				currentFunction = ""
				nsb
      }

      case _ => sb.append("Defn?")
    }
  }
  
  //generates an isabelle file corresponding to the scala input program
  def analyse(program : Program) : Unit = {
    val file = new FileOutputStream("isabelle_examples/translation/" + program.mainObject.id +  ".thy")
    val out = new PrintStream(file)
    out.println(apply(program))
    reporter.info(apply(program))
    out.close()    
  }

}
