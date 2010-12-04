package magpie

trait precategory[h <: hom.set] {
  def compose[A>:h#inf<:h#sup, B>:h#inf<:h#sup, C>:h#inf<:h#sup](f : h#hom[B,C], g: h#hom[A,B]) : h#hom[A,C]
  def dual : precategory[hom.set.dual[h]] = precategory.op(this)
}
  
object precategory { 
  import equality._
  def duality[h<:hom.set] : precategory[h] === precategory[hom.set.dual[hom.set.dual[h]]] = 
     hom.set.duality[h].lift[Nothing,Any,({type λ[x<:hom.set] = precategory[x]})#λ]

  trait op[h <: hom.set] extends precategory[hom.set.dual[h]] { 
    def compose[A>:h#inf<:h#sup, B>:h#inf<:h#sup, C>:h#inf<:h#sup](f : h#hom[C,B], g: h#hom[B,A]) : h#hom[C,A] = dual.compose[C,B,A](g, f)
  }
  object op { 
    def apply[h<:hom.set](c : precategory[h]) : op[h] = new op[h] {
      override def dual : precategory[hom.set.dual[hom.set.dual[h]]] = witness(duality[h])(c)
    }
  }
}
