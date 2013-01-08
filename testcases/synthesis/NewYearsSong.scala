import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object NewYearSong {

  def computeLines(eLines: Int,
		 iLines: Int,
		 iSyls: Int,
		 nSyls: Int) : (Int,Int,Int,Int,Int,Int) = {
  choose((line7: Int, 
	  line8: Int, 
	  nsLines: Int, 
	  nLines: Int, 
	  tLines: Int, 
	  tLinesFact: Int) => (
            tLines == eLines + nLines
            && nLines == iLines + nsLines
            && nLines == line7 + line8
            && nSyls + iSyls == 7 * line7 + 8 * line8
            && tLines == 4 * tLinesFact // expresses (4 | tLines)
            && line8 >= 0
            && line7 >= 0
            && tLines >= 0
          ))
  }

}
