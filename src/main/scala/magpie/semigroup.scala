package magpie

trait semigroup[m] extends magma[m] {
  override def dual : semigroup[m] = semigroup.op(this)
  def *[n](that: semigroup[n]) : semigroup.product[m,n] = semigroup.product[m,n](this,that)
}

object semigroup {
  /** A construct a semigroup from an associative binary function */
  def apply[m](f:(m,m)=>m) : semigroup[m] = new semigroup[m] { 
    def add(a: m, b: m):m = f(a,b)
  }

  trait op[m] extends semigroup[m] { 
    def add(a: m, b: m) = dual.add(b,a)
  }
  object op { 
    def apply[m](c : semigroup[m]) : op[m] = new op[m] {
      override def dual: semigroup[m] = c
    }
  }

  trait product[m,n] extends magma.product[m,n] with phantom.product[semigroup[m], semigroup[n]] {
    override def _1: semigroup[m]
    override def _2: semigroup[n]
    override def dual: semigroup.product[m,n] = semigroup.product[m,n](_1.dual,_2.dual)
  } 
  object product {
    def apply[m,n](m: semigroup[m], n: semigroup[n]): product[m,n] = new product[m,n] {
      def _1: semigroup[m] = m
      def _2: semigroup[n] = n
    }
  }
}
