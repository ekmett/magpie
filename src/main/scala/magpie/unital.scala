package magpie

trait unital[m] {
  def zero: m
  def dual: unital[m] = this
  def *[n](that: unital[n]): unital.product[m,n] = unital.product[m,n](this,that)
}

object unital {
  /** A construct a monoid from a zero and a binary function */
  def apply[m](m:m): unital[m] = new unital[m] { 
    def zero: m = m
  }

  trait product[m,n] extends unital[typed.product[m,n]] with phantom.product[unital[m], unital[n]] {
    def _1: unital[m]
    def _2: unital[n]
    def zero: typed.product[m,n] = typed.product(_1.zero,_2.zero)
    override def dual: unital.product[m,n] = unital.product[m,n](_1.dual,_2.dual)
  } 
  object product {
    def apply[m,n](m: unital[m], n: unital[n]): product[m,n] = new product[m,n] {
      def _1: unital[m] = m
      def _2: unital[n] = n
    }
  }
}
