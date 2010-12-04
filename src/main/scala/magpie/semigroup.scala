package magpie

trait semigroup[m] extends magma[m] {
  override def dual : semigroup[m] = semigroup.op(this)
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
      override def dual : semigroup[m] = c
    }
  }
}
