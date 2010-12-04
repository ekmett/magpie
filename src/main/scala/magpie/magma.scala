package magpie

trait magma[m] {
  def add(a: m, b: m): m
  def dual : magma[m] = magma.op(this)
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
}
