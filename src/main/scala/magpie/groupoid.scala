package magpie

trait groupoid[h <: hom.set] extends category[h] { 
  def inv[A>:h#inf<:h#sup,B>:h#inf<:h#sup](f: h#hom[A,B]) : h#hom[B,A]
  override def dual : groupoid[hom.set.dual[h]] = groupoid.op(this)
}

object groupoid {
  import magpie.equality._

  def duality[h<:hom.set] : groupoid[h] === groupoid[hom.set.dual[hom.set.dual[h]]] = 
     hom.set.duality[h].lift[Nothing,Any,({type λ[x<:hom.set] = groupoid[x]})#λ]

  trait op[h <: hom.set] extends groupoid[hom.set.dual[h]] with category.op[h] { 
     def inv[a>:h#inf<:h#sup,b>:h#inf<:h#sup](f: h#hom[b,a]) : h#hom[a,b] = dual.inv[b,a](f)
  }

  object op { 
    def apply[h<:hom.set](c : groupoid[h]) : op[h] = new op[h] {
      override def dual : groupoid[hom.set.dual[hom.set.dual[h]]] = witness(duality[h])(c)
    }
  }

  /** equality forms a groupoid */
  def equality[l,h>:l] : groupoid[hom.set.of[l,h,({type λ[a>:l<:h,b>:l<:h]=equality[l,h,a,b]})#λ]] =
                     new groupoid[hom.set.of[l,h,({type λ[a>:l<:h,b>:l<:h]=equality[l,h,a,b]})#λ]] {
    def id[a>:l<:h] = refl[a]
    def compose[a>:l<:h,b>:l<:h,c>:l<:h](f: equality[l,h,b,c], g: equality[l,h,a,b]): equality[l,h,a,c] = trans[l,h,a,b,c](f,g)
    def inv[a>:l<:h,b>:l<:h](a: equality[l,h,a,b]) = symm[l,h,a,b](a)
  }
}
