package magpie

trait magma[m] extends precategory[hom.set.singleton[m]] {
  def compose[a>:m<:m,b>:m<:m,c>:m<:m](f: m, g: m) : m = add(f,g)
  def add(a: m, b: m): m
  override def dual : magma[m] = magma.op(this)
  def *[n](that: magma[n]) : magma.product[m,n] = magma.product[m,n](this,that)
}

object magma {
  /** A construct a monoid from a zero and a binary function */
  def apply[m](f:(m,m)=>m): magma[m] = new magma[m] { 
    def add(a: m, b: m):m = f(a,b)
  }

  trait op[m] extends magma[m] { 
    def add(a: m, b: m) = dual.add(b,a)
  }
  object op { 
    def apply[m](c : magma[m]) : op[m] = new op[m] {
      override def dual : magma[m] = c
    }
  }

  trait product[m,n] extends magma[typed.product[m,n]] with phantom.product[magma[m], magma[n]] {
    def _1: magma[m]
    def _2: magma[n]
    def add(a: typed.product[m,n], b: typed.product[m,n]): typed.product[m,n] = typed.product(_1.add(a._1,b._1),_2.add(a._2,b._2))
    override def dual: magma.product[m,n] = magma.product[m,n](_1.dual,_2.dual)
  } 
  object product {
    def apply[m,n](m: magma[m], n: magma[n]): product[m,n] = new product[m,n] {
      def _1: magma[m] = m
      def _2: magma[n] = n
    }
  }
}
