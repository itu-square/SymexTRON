package helper

/**
 * Created by asal on 06/10/2015.
 */
class Counter(value : Int) extends Ref[Int](value) {
  def +=(diff : Int) = {
    val oldValue = !this
    this := oldValue + diff
    oldValue
  }

  def -=(diff : Int) = {
    this += -diff
  }

  def ++() = {
    this += 1
  }

  def --() = {
    this -= 1
  }
}

object Counter {
  def apply(value : Int) = new Counter(value)
}
