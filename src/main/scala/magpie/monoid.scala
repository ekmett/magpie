package magpie

trait monoid[m] extends category[hom.set.singleton[m]] with semigroup[m] with unital[m] {
  def id[a>:m<:m] = zero
  override def dual : monoid[m] = monoid.op(this)
  def *[n](that: monoid[n]) : monoid.product[m,n] = monoid.product[m,n](this,that)
}

object monoid {
  /** A construct a monoid from a zero and a binary function */
  def apply[m](z: m,f:(m,m)=>m) : monoid[m] = new monoid[m] { 
    def add(a: m, b: m):m = f(a,b)
    def zero: m = z
  }

  trait op[m] extends monoid[m] with semigroup.op[m] { 
    def zero: m = dual.zero
  }

  object op { 
    def apply[m](c : monoid[m]) : op[m] = new op[m] {
      override def dual : monoid[m] = c
    }
  }

  def multiplication[n](implicit num: Numeric[n]) : monoid[n] = new monoid[n] {
    def add(a:n,b:n) = num.times(a,b)
    def zero = num.one
  }
  trait product[m,n] 
    extends category.product[hom.set.singleton[m],hom.set.singleton[n]] 
       with semigroup.product[m,n]
       with unital.product[m,n]
       with phantom.product[monoid[m], monoid[n]] {
    def _1: monoid[m]
    def _2: monoid[n]
    type mn = typed.product[m,n]
    override def id[a>:mn<:mn] = zero
    override def compose[a>:mn<:mn,b>:mn<:mn,c>:mn<:mn](f: mn, g: mn) : mn = add(f,g)
    override def dual = product[m,n](_1.dual,_2.dual)
  }
  object product {
    def apply[m,n](m: monoid[m], n: monoid[n]): product[m,n] = new product[m,n] {
      def _1: monoid[m] = m
      def _2: monoid[n] = n
    }
  }
}

