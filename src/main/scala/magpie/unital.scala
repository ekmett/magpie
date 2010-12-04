package magpie

trait unital[m] {
  def zero: m
}

object unital {
  /** A construct a monoid from a zero and a binary function */
  def apply[m](m:m): unital[m] = new unital[m] { 
    def zero: m = m
  }
}
