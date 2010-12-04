package magpie

import equality.{ ===, refl } 
import hom.set.dual 

trait algebra[h<:hom.set, f[_>:h#inf<:h#sup]>:h#inf<:h#sup, a>:h#inf<:h#sup] { 
  def functor: endofunctor[h,f]
  def morphism: h#hom[f[a],a]
  def dual: coalgebra[hom.set.dual[h],f,a] = coalgebra.op[h,f,a](this)
  // def *[h2<:hom.set,g[_>:h2#inf<:h2#sup]>:h2#inf<:h2#sup, b >:h2#inf<:sup](that: algebra[h2,g,b]) : algebra[hom.set.product[h,h2],functor * that.functor, typed.product[a,b]]
}

object algebra { 
  def duality[
    carrier<:hom.set,
    f[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup,
    a>:carrier#inf<:carrier#sup
  ]:algebra[carrier,f,a] === algebra[dual[dual[carrier]],f,a] = refl[algebra[carrier,f,a]].asInstanceOf[
    algebra[carrier,f,a] === algebra[dual[dual[carrier]],f,a]
  ]
  trait op[h<:hom.set, f[_>:h#inf<:h#sup]>:h#inf<:h#sup,a>:h#inf<:h#sup] extends algebra[dual[h],f,a] {
    def functor: endofunctor[dual[h],f] = dual.functor.dual
    def morphism: h#hom[a,f[a]] = dual.morphism
  }
  object op { 
    def apply[h<:hom.set, f[_>:h#inf<:h#sup]>:h#inf<:h#sup,a>:h#inf<:h#sup](f: coalgebra[h,f,a]) : op[h,f,a] = new op[h,f,a] { 
      override def dual = coalgebra.duality[h,f,a](f)
    }
  }
}


trait coalgebra[h<:hom.set, f[_>:h#inf<:h#sup]>:h#inf<:h#sup, a>:h#inf<:h#sup] {
  def functor: endofunctor[h,f]
  def morphism: h#hom[a,f[a]]
  def dual: algebra[hom.set.dual[h],f,a] = algebra.op[h,f,a](this)
}

object coalgebra { 
  def duality[
    carrier<:hom.set,
    f[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup,
    a>:carrier#inf<:carrier#sup
  ]:coalgebra[carrier,f,a] === coalgebra[dual[dual[carrier]],f,a] = refl[coalgebra[carrier,f,a]].asInstanceOf[
    coalgebra[carrier,f,a] === coalgebra[dual[dual[carrier]],f,a]
  ]
  trait op[h<:hom.set, f[_>:h#inf<:h#sup]>:h#inf<:h#sup,a>:h#inf<:h#sup] extends coalgebra[dual[h],f,a] { 
    def functor: endofunctor[dual[h],f] = dual.functor.dual
    def morphism: h#hom[f[a],a] = dual.morphism
  }
  object op { 
    def apply[h<:hom.set, f[_>:h#inf<:h#sup]>:h#inf<:h#sup,a>:h#inf<:h#sup](f: algebra[h,f,a]) : op[h,f,a] = new op[h,f,a] {
      override def dual = algebra.duality[h,f,a](f)
    }
  }
}
