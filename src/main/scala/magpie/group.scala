package magpie

trait group[m] extends monoid[m] with groupoid[hom.set.singleton[m]] {
  final def inv[a>:m<:m,b>:m<:m](m: m) = negate(m)
  def negate(m:m):m 
  override def dual : group[m] = group.op(this)
}

object group {
  trait op[m] extends group[m] with monoid.op[m] {
    def negate(m:m):m = dual.negate(m)
  }
  object op { 
    def apply[m](c : group[m]) : op[m] = new op[m] {
      override def dual : group[m] = c
    }
  }
  def addition[n](implicit num: Numeric[n]) : group[n] = new group[n] {
    def add(a:n,b:n) = num.plus(a,b)
    def zero = num.zero
    def negate(a:n) = num.negate(a)
  }
}

