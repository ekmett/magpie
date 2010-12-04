package magpie

trait precategory[h <: hom.set] {
  def compose[A>:h#inf<:h#sup, B>:h#inf<:h#sup, C>:h#inf<:h#sup](f : h#hom[B,C], g: h#hom[A,B]) : h#hom[A,C]
  def dual : precategory[hom.set.dual[h]] = precategory.op(this)
  def *[g <: hom.set](that: precategory[g]) : precategory.product[h,g] = precategory.product[h,g](this,that)
}
  
object precategory { 
  import equality.{ === } 
  import subtype.{ <~< }

  def duality[h<:hom.set] : precategory[h] === precategory[hom.set.dual[hom.set.dual[h]]] = 
     hom.set.duality[h].lift[Nothing,Any,({type λ[x<:hom.set] = precategory[x]})#λ]

  trait op[h <: hom.set] extends precategory[hom.set.dual[h]] { 
    def compose[A>:h#inf<:h#sup, B>:h#inf<:h#sup, C>:h#inf<:h#sup](f : h#hom[C,B], g: h#hom[B,A]) : h#hom[C,A] = dual.compose[C,B,A](g, f)
  }
  object op { 
    def apply[h<:hom.set](c : precategory[h]) : op[h] = new op[h] {
      override def dual : precategory[hom.set.dual[hom.set.dual[h]]] = 
          duality[h](c)
    }
  }

  trait product[m<:hom.set,n<:hom.set] extends 
        precategory[hom.set.product[m,n]] with 
        phantom.product[precategory[m], precategory[n]] {
    def _1: precategory[m]
    def _2: precategory[n]
    type h = hom.set.product[m,n]
    def compose[A>:h#inf<:h#sup, B>:h#inf<:h#sup, C>:h#inf<:h#sup](f : h#hom[B,C], g: h#hom[A,B]) : h#hom[A,C] = 
     // hom.product[m,n,A,C]
     typed.product(
       _1.compose[A#_1,B#_1,C#_1](f._1,g._1),
       _2.compose[A#_2,B#_2,C#_2](f._2,g._2)
     )
    override def dual =
        product.duality[m,n](product[hom.set.dual[m],hom.set.dual[n]](_1.dual,_2.dual))
  } 
  object product {
    def apply[m<:hom.set,n<:hom.set](m: precategory[m], n: precategory[n]): product[m,n] = new product[m,n] {
      def _1: precategory[m] = m
      def _2: precategory[n] = n
    }
    def duality[m<:hom.set,n<:hom.set] 
    : precategory[hom.set.product[hom.set.dual[m],hom.set.dual[n]]] <~<
      precategory[hom.set.dual[hom.set.product[m,n]]] = 
      hom.set.product.duality[m,n].lift[Nothing,Any,({type λ[+x<:hom.set] = precategory[x]})#λ]
  }
}
