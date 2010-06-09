package purescala

import Definitions._
import Trees._

object Analysis {
    // Analysis should check that:
    //  - all the postconditions are implied by preconds. + body
    //  - all callsites satisfy the preconditions
    //  - all matches are exhaustive
    // In the future:
    //  - catamorphisms are catamorphisms (poss. with surjectivity conds.)
    //  - injective functions are injective
    //  - all global invariants are satisfied 
    def analyze(program: Program) : Unit = {
        program.mainObject.defs.filter(_.isInstanceOf[FunDef]).foreach(df => {
            val funDef = df.asInstanceOf[FunDef]
            val vc = postconditionVC(funDef)
            if(vc != BooleanLiteral(true)) {
                println("Verification condition for " + funDef.id + ":")
                println(vc)
            }
        }) 
    }

    def postconditionVC(functionDefinition: FunDef) : Expr = {
        val prec = functionDefinition.precondition
        val post = functionDefinition.postcondition

        if(post.isEmpty) {
            BooleanLiteral(true)
        } else {
            BooleanLiteral(false)
        }
    }
}
