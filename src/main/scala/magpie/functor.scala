package magpie

// -dom,+cod
trait functor[dom<:hom.set,cod<:hom.set,f[_>:dom#inf<:dom#sup]>:cod#inf<:cod#sup] {
  def dom : category[dom]
  def cod : category[cod]
  def apply[a>:dom#inf<:dom#sup, b>:dom#inf<:dom#sup](f: dom#hom[a,b]): cod#hom[f[a],f[b]]
  def dual : functor[hom.set.dual[dom], hom.set.dual[cod], f] = functor.op[dom,cod,f](this)

  /* TODO: this really should assert that the interim category is the same */
  def compose[pre<:hom.set,g[_>:pre#inf<:pre#sup]>:dom#inf<:dom#sup](
    that: functor[pre,dom,g]
  ) : functor[pre,cod,({type λ[x>:pre#inf<:pre#sup] = f[g[x]]})#λ] = 
  new functor[pre,cod,({type λ[x>:pre#inf<:pre#sup] = f[g[x]]})#λ] {
    def dom : category[pre] = that.dom
    def cod : category[cod] = functor.this.cod
    def apply[
      a>:pre#inf<:pre#sup, 
      b>:pre#inf<:pre#sup
    ](f: pre#hom[a,b]): cod#hom[f[g[a]],f[g[b]]] = functor.this.apply[g[a],g[b]](that.apply[a,b](f))
  }
}

object functor {
  import equality._
  import hom.set._
  def duality[
    dom<:hom.set,
    cod<:hom.set,
    f[_>:dom#inf<:dom#sup]>:cod#inf<:cod#sup
  ]:functor[dom,cod,f] === functor[dual[dual[dom]],dual[dual[cod]],f] = refl[functor[dom,cod,f]].asInstanceOf[
    functor[dom,cod,f] === functor[dual[dual[dom]],dual[dual[cod]],f]
  ]

  trait op[dom<:hom.set, cod<:hom.set, f[_>:dom#inf<:dom#sup]>:cod#inf<:cod#sup] extends functor[hom.set.dual[dom], hom.set.dual[cod], f] {
    def dom : category[hom.set.dual[dom]] = dual.dom.dual
    def cod : category[hom.set.dual[cod]] = dual.cod.dual
    def apply[a>:dom#inf<:dom#sup, b>:dom#inf<:dom#sup](f: dom#hom[b,a]): cod#hom[f[b],f[a]] = dual[b,a](f)
  }
  object op {
    def apply[dom<:hom.set,cod<:hom.set, f[_>:dom#inf<:dom#sup]>:cod#inf<:cod#sup](f: functor[dom,cod,f]) : op[dom,cod,f] = new op[dom,cod,f] { 
      override def dual : functor[dual[dual[dom]], dual[dual[cod]], f] = witness(duality[dom,cod,f])(f)
    }
  }
}

/* TODO: a more correct duality:
 hom.set.duality[cod].inverse.subst[({type λ[x<:hom.set]=functor[dom,x,f]===functor[dual[dual[dom]],dual[dual[cod]],f]})#λ](hom.set.duality[dom].inverse.subst[({type λ[x<:hom.set]=functor[x,dual[dual[cod]],f]===functor[dual[dual[dom]],dual[dual[cod]],f]})#λ](refl[functor[dual[dual[dom]],dual[dual[cod]],f]]))
*/

