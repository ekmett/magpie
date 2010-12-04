package magpie

trait category[h <: hom.set] extends precategory[h] {
  def id[A>:h#inf<:h#sup]: h#hom[A,A]
  override def dual : category[hom.set.dual[h]] = category.op(this)
  def *[g <: hom.set](that: category[g]) : category.product[h,g] = category.product[h,g](this,that)
}
  
object category { 
  import equality.{ === } 
  def duality[h<:hom.set] : category[h] === category[hom.set.dual[hom.set.dual[h]]] = 
     hom.set.duality[h].lift[Nothing,Any,({type λ[x<:hom.set] = category[x]})#λ]

  trait op[h <: hom.set] extends category[hom.set.dual[h]] with precategory.op[h] { 
    def id[A>:h#inf<:h#sup]: h#hom[A,A] = dual.id[A]
  }

  object op { 
    def apply[h<:hom.set](c : category[h]) : op[h] = new op[h] {
      override def dual : category[hom.set.dual[hom.set.dual[h]]] = duality[h](c)
    }
  }
  trait product[m<:hom.set,n<:hom.set] extends 
        precategory.product[m,n] with 
        category[hom.set.product[m,n]] with 
        phantom.product[category[m], category[n]] {
    def _1: category[m]
    def _2: category[n]
    // type h = hom.set.product[m,n] -- defined in precategory.product
    def id[A>:h#inf<:h#sup]: h#hom[A,A] = typed.product(_1.id[A#_1],_2.id[A#_2])
    override def dual = product.duality[m,n](product[hom.set.dual[m],hom.set.dual[n]](_1.dual,_2.dual))
  } 
  object product {
    def apply[m<:hom.set,n<:hom.set](m: category[m], n: category[n]): product[m,n] = new product[m,n] {
      def _1: category[m] = m
      def _2: category[n] = n
    }
    import subtype.{ <~< }
    def duality[m<:hom.set,n<:hom.set] 
    : category[hom.set.product[hom.set.dual[m],hom.set.dual[n]]] <~<
      category[hom.set.dual[hom.set.product[m,n]]] = 
      hom.set.product.duality[m,n].lift[Nothing,Any,({type λ[+x<:hom.set] = category[x]})#λ]
  }
}

