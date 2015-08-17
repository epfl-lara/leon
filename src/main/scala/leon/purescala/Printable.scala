package leon
package purescala


trait Printable {
  def asString(implicit ctx: LeonContext): String
}
