package magpie

trait groupoid[h <: hom.set] extends category[h] { 
  def inv[A>:h#inf<:h#sup,B>:h#inf<:h#sup](f: h#hom[A,B]) : h#hom[B,A]
  override def dual : groupoid[hom.set.dual[h]] = groupoid.op(this)
  def *[g <: hom.set](that: groupoid[g]) : groupoid.product[h,g] = groupoid.product[h,g](this,that)
}

object groupoid {
  import magpie.equality.{ === } 

  def duality[h<:hom.set] : groupoid[h] === groupoid[hom.set.dual[hom.set.dual[h]]] = 
     hom.set.duality[h].lift[Nothing,Any,({type λ[x<:hom.set] = groupoid[x]})#λ]

  trait op[h <: hom.set] extends groupoid[hom.set.dual[h]] with category.op[h] { 
     def inv[a>:h#inf<:h#sup,b>:h#inf<:h#sup](f: h#hom[b,a]) : h#hom[a,b] = dual.inv[b,a](f)
  }

  object op { 
    def apply[h<:hom.set](c : groupoid[h]) : op[h] = new op[h] {
      override def dual : groupoid[hom.set.dual[hom.set.dual[h]]] = duality[h](c)
    }
  }

  /** equality forms a groupoid */
  def equality[l,h>:l] : groupoid[hom.set.of[l,h,({type λ[a>:l<:h,b>:l<:h]=equality[l,h,a,b]})#λ]] =
                     new groupoid[hom.set.of[l,h,({type λ[a>:l<:h,b>:l<:h]=equality[l,h,a,b]})#λ]] {
    def id[a>:l<:h] = magpie.equality.refl[a]
    def compose[a>:l<:h,b>:l<:h,c>:l<:h](f: equality[l,h,b,c], g: equality[l,h,a,b]): equality[l,h,a,c] = magpie.equality.trans[l,h,a,b,c](f,g)
    def inv[a>:l<:h,b>:l<:h](a: equality[l,h,a,b]) : equality[l,h,b,a] = magpie.equality.symm[l,h,a,b](a)
  }

  trait product[m<:hom.set,n<:hom.set] extends 
        category.product[m,n] with 
        groupoid[hom.set.product[m,n]] with 
        phantom.product[groupoid[m], groupoid[n]] {
    def _1: groupoid[m]
    def _2: groupoid[n]
    // type h = hom.set.product[m,n] -- defined in precategory.product
    def inv[A>:h#inf<:h#sup,B>:h#inf<:h#sup](f: h#hom[A,B]): h#hom[B,A] = typed.product(_1.inv[A#_1,B#_1](f._1),_2.inv[A#_2,B#_2](f._2))
    override def dual =
        product.duality[m,n](product[hom.set.dual[m],hom.set.dual[n]](_1.dual,_2.dual))
  } 
  object product {
    def apply[m<:hom.set,n<:hom.set](m: groupoid[m], n: groupoid[n]): product[m,n] = new product[m,n] {
      def _1: groupoid[m] = m
      def _2: groupoid[n] = n
    }
    import magpie.subtype.{ <~< }
    def duality[m<:hom.set,n<:hom.set] 
    : groupoid[hom.set.product[hom.set.dual[m],hom.set.dual[n]]] <~<
      groupoid[hom.set.dual[hom.set.product[m,n]]] = 
      hom.set.product.duality[m,n].lift[Nothing,Any,({type λ[+x<:hom.set] = groupoid[x]})#λ]
  }
}

