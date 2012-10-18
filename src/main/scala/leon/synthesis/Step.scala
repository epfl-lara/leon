package leon
package synthesis

case class Step(subProblems: List[Problem], construct: List[Solution] => Solution, score: Score);
