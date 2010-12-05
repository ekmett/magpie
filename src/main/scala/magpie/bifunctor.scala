package magpie

// sugar for functors from C x D -> E
trait bifunctor[l<:hom.set,
                r<:hom.set,
                cod<:hom.set,
                f[_>:hom.set.product[l,r]#inf<:hom.set.product[l,r]#sup]>:cod#inf<:cod#sup] extends 
      functor[hom.set.product[l,r],cod,f] {
  type dom = hom.set.product[l,r]
  def dom : category.product[l,r]

  type _1[b>:r#inf<:r#sup] = functor[l,cod,({type λ[x>:l#inf<:l#sup] = f[typed.product[x,b]]})#λ] 
  type _2[a>:l#inf<:l#sup] = functor[r,cod,({type λ[x>:r#inf<:r#sup] = f[typed.product[a,x]]})#λ]

  def _1[b>:r#inf<:r#sup] : _1[b]
  def _2[a>:l#inf<:l#sup] : _2[a]

/*
  def apply[a>:dom#inf<:dom#sup, b>:dom#inf<:dom#sup](
    f: dom#hom[a,b]
  )  : cod#hom[f[a],f[b]] = 
    bimap[a#_1,b#_1,a#_2,b#_2](f._1,f._2)

  def bimap[
    a>:l#inf<:l#sup,b>:l#inf<:l#sup,
    c>:r#inf<:r#sup,d>:r#inf<:r#sup
  ](f: l#hom[a,b], g: r#hom[c,d]) : cod#hom[f[typed.product[a,c]],f[typed.product[b,d]]]

  def dual : bifunctor[hom.set.dual[l],hom.set.dual[r],homset.dual[cod], hom.set.dual[cod], f] 
*/
}

