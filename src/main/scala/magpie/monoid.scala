package magpie

trait monoid[m] extends category[hom.set.singleton[m]] with semigroup[m] with unital[m] {
  final def id[a>:m<:m] = zero
  final def compose[a>:m<:m,b>:m<:m,c>:m<:m](f: m, g: m) : m = add(f,g)
  override def dual : monoid[m] = monoid.op(this)
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
}
