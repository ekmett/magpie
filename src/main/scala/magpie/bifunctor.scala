package magpie

// sugar for functors from C x D -> E
trait bifunctor[
  l<:hom.set,
  r<:hom.set,
  cod<:hom.set,
  F[+_>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup]>:cod#inf<:cod#sup
] extends functor[hom.set.product[l,r],cod,F] { base => 

  type dom = hom.set.product[l,r]
  def dom : category.product[l,r]

  def apply[
    a>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup,
    b>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup,
    c>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup,
    d>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup
  ](
    f: dom#dihom[a,b,c,d]
    // f: typed.product[l#dihom[a#_1,b#_1,c#_1,d#_1], r#dihom[a#_2,b#_2,c#_2,d#_2]]
  ) : cod#dihom[F[a],F[b],F[c],F[d]]
    = bimap[a#_1,b#_1,c#_1,d#_1,a#_2,b#_2,c#_2,d#_2](f._1, f._2)
      .asInstanceOf[cod#dihom[F[a],F[b],F[c],F[d]]] // why, god, why!?

  type _1[b>:r#inf<:r#sup] = functor[l,cod,({type λ[+x>:l#inf<:l#sup] = F[typed.product[x,b]]})#λ] 
  def _1[B>:r#inf<:r#sup] : _1[B] = new functor[l,cod,({type λ[+x>:l#inf<:l#sup] = F[typed.product[x,B]]})#λ] {
    def dom = base.dom._1
    def cod = base.cod
    def apply[
      a>:l#inf<:l#sup,
      b>:l#inf<:l#sup,
      c>:l#inf<:l#sup,
      d>:l#inf<:l#sup
    ](f: l#dihom[a,b,c,d]) = base.bimap[a,b,c,d,B,B,B,B](f, base.dom._2.id[B])
  }

  type _2[a>:l#inf<:l#sup] = functor[r,cod,({type λ[+x>:r#inf<:r#sup] = F[typed.product[a,x]]})#λ]
  def _2[A>:l#inf<:l#sup] : _2[A] = new functor[r,cod,({type λ[+x>:r#inf<:r#sup] = F[typed.product[A,x]]})#λ] {
    def dom = base.dom._2
    def cod = base.cod
    def apply[
      a>:r#inf<:r#sup,
      b>:r#inf<:r#sup,
      c>:r#inf<:r#sup,
      d>:r#inf<:r#sup
    ](f: r#dihom[a,b,c,d]) = base.bimap[A,A,A,A,a,b,c,d](base.dom._1.id[A], f)
  }


  def bimap[
    a>:l#inf<:l#sup, b>:l#inf<:l#sup,
    c>:l#inf<:l#sup, d>:l#inf<:l#sup,
    e>:r#inf<:r#sup, f>:r#inf<:r#sup,
    g>:r#inf<:r#sup, h>:r#inf<:r#sup
  ](
    f: l#dihom[a,b,c,d],
    g: r#dihom[e,f,g,h]
  ) : cod#dihom[F[typed.product[a,e]],
                F[typed.product[b,f]],
                F[typed.product[c,g]],
                F[typed.product[d,h]]]
  /*
   = apply[typed.product[a,e], 
           typed.product[b,f],
           typed.product[c,g],
           typed.product[d,h]
          ](typed.product[l#dihom[a,b,c,d],r#dihom[e,f,g,h]](f,g))
  */

  // override def dual : functor[hom.set.product[hom.set.dual[l],hom.set.dual[r]],hom.set.dual[cod], f] with 
  //                     bifunctor[hom.set.dual[l],hom.set.dual[r],hom.set.dual[cod], f] 
}

object bifunctor {
  


}

