package magpie

/** 
 * A pre-category is defined to provide a possibly non-associative composition 
 * This terminology collides with another 'precategory' notion which usually just provides
 * arrows and doesn't even provide composition, relying instead upon the construction of paths.
 *
 * We choose to start here instead.
 */ 
trait precategory[h <: hom.set] {
  def compose[A>:h#inf<:h#sup, B>:h#inf<:h#sup, C>:h#inf<:h#sup](f : h#hom[B,C], g: h#hom[A,B]) : h#hom[A,C]
  def dual : precategory[hom.set.dual[h]] // = precategory.op(this)
  // def *[g <: hom.set](that: precategory[g]) : precategory.product[h,g] = precategory.product[h,g](this,that)
}
  
object precategory { 
  import equality.{ === } 

  def duality[h<:hom.set] : precategory[h] === precategory[hom.set.dual[hom.set.dual[h]]] = 
     hom.set.duality[h].lift[Nothing,Any,({type λ[x<:hom.set] = precategory[x]})#λ]

/*
  trait op[h <: hom.set] extends precategory[hom.set.dual[h]] { 
    // def compose[A>:hom.set.dual[h]#inf<:hom.set.dual[h]#sup, B>:hom.set.dual[h]#inf<:hom.set.dual[h]#sup, C>:hom.set.dual[h]#inf<:hom.set.dual[h]#sup](f : hom.set.dual[h]#hom[C,B], g: hom.set.dual[h]#hom[A,B]) : hom.set.dual[h]#hom[A,C] = dual.compose[A,B,C](g, f)
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
    import subtype.{ <~< }
    def duality[m<:hom.set,n<:hom.set] 
    : precategory[hom.set.product[hom.set.dual[m],hom.set.dual[n]]] <~<
      precategory[hom.set.dual[hom.set.product[m,n]]] = 
      hom.set.product.duality[m,n].colift[Nothing,Any,({type λ[+x<:hom.set] = precategory[x]})#λ]
  }
*/
}
