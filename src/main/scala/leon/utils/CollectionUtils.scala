/* Copyright 2009-2017 EPFL, Lausanne */

package leon.utils

import scala.collection.mutable

object CollectionUtils {

  implicit class MutableMapUtils[K, V](map: mutable.Map[K, V]) {
    def orElseUpdate(key: K, optValue: => Option[V]): Option[V] = {
      map.get(key).orElse {
        val ov = optValue
        ov foreach (map.update(key, _))
        ov
      }
    }
  }
}