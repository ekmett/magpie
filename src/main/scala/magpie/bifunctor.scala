package magpie

// sugar for functors from C x D -> E
trait bifunctor[
  l<:hom.set,
  r<:hom.set,
  cod<:hom.set,
  F[+_>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup]>:cod#inf<:cod#sup
] extends functor[hom.set.product[l,r],cod,F] { base => 


  def l : category[l]
  def r : category[r]
  type dom = hom.set.product[l,r]
  def dom : category.product[l,r] = category.product(l,r)

  def bimap[
    a>:l#inf<:l#sup, b>:l#inf<:l#sup,
    e>:r#inf<:r#sup, f>:r#inf<:r#sup
  ](
    f: hom.C[l,a,b],
    g: hom.C[r,e,f]
  ) : hom.C[cod,F[typed.product[a,e]], F[typed.product[b,f]]]

  def apply[
    a>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup,
    b>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup
  ](
    f: hom.C[dom,a,b]
  ) : hom.C[cod,F[a],F[b]]
    = bimap[a#_1,b#_1,a#_2,b#_2](f._1, f._2)
      .asInstanceOf[hom.C[cod,F[a],F[b]]] // seriously, WTF

  type _1[b>:r#inf<:r#sup] = functor[l,cod,({type λ[+x>:l#inf<:l#sup] = F[typed.product[x,b]]})#λ] 
  def _1[B>:r#inf<:r#sup] : _1[B] = new functor[l,cod,({type λ[+x>:l#inf<:l#sup] = F[typed.product[x,B]]})#λ] {
    def dom = base.dom._1
    def cod = base.cod
    def apply[
      a>:l#inf<:l#sup,
      b>:l#inf<:l#sup
    ](f: hom.C[l,a,b]) = base.bimap[a,b,B,B](f, base.dom._2.id[B])
  }

  type _2[a>:l#inf<:l#sup] = functor[r,cod,({type λ[+x>:r#inf<:r#sup] = F[typed.product[a,x]]})#λ]
  def _2[A>:l#inf<:l#sup] : _2[A] = new functor[r,cod,({type λ[+x>:r#inf<:r#sup] = F[typed.product[A,x]]})#λ] {
    def dom = base.dom._2
    def cod = base.cod
    def apply[
      a>:r#inf<:r#sup,
      b>:r#inf<:r#sup
    ](f: hom.C[r,a,b]) = base.bimap[A,A,a,b](base.dom._1.id[A], f)
  }
}

object bifunctor {
  def tuple : bifunctor[hom.set.scala, hom.set.scala, hom.set.scala,({type λ[+A>:typed.product[Nothing,Nothing]<:typed.product[Any,Any]] = A })#λ]
        = new bifunctor[hom.set.scala, hom.set.scala, hom.set.scala,({type λ[+A>:typed.product[Nothing,Nothing]<:typed.product[Any,Any]] = A })#λ] {
    def l = category.scala 
    def r = category.scala
    def cod = category.scala
    def bimap[a,b,e,f](f: a => b, g: e => f) 
      : typed.product[a,e] => typed.product[b,f]
      = (ae: typed.product[a,e]) => typed.product[b,f](f(ae._1),g(ae._2))
  }
}

