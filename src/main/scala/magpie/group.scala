package magpie

trait group[m] extends monoid[m] with groupoid[hom.set.singleton[m]] {
  def inv[a>:m<:m,b>:m<:m](m: m) = negate(m)
  def negate(m:m):m 
  override def dual : group[m] = group.op(this)
  def *[n](that: group[n]) : group.product[m,n] = group.product[m,n](this,that)
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

  trait product[m,n] 
    extends monoid.product[m,n]
       with groupoid.product[hom.set.singleton[m],hom.set.singleton[n]]
       with group[typed.product[m,n]]
       with phantom.product[group[m],group[n]] {
    def _1: group[m]
    def _2: group[n]
    // type mn = typed.product[m,n]
    override def inv[a>:mn<:mn,b>:mn<:mn](mn: mn) = negate(mn)
    override def id[a>:mn<:mn] = zero
    override def compose[a>:mn<:mn,b>:mn<:mn,c>:mn<:mn](f: mn, g: mn) : mn = add(f,g)
    override def dual = product[m,n](_1.dual,_2.dual)

    override def negate(mn:mn) = typed.product(_1.negate(mn._1),_2.negate(mn._2))
  }
  object product {
    def apply[m,n](m: group[m], n: group[n]): product[m,n] = new product[m,n] {
      def _1: group[m] = m
      def _2: group[n] = n
    }
  }
}

