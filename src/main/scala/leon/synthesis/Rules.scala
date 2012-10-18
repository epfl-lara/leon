package leon
package synthesis

/** AST definitions for Pure Scala. */
object Rules {

  abstract class Rule {
    def isApplicable(p: Problem): Option[Step];
  }

}
