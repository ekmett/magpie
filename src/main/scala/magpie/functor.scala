package magpie

trait functor[dom<:hom.set,cod<:hom.set,f[+_>:dom#inf<:dom#sup]>:cod#inf<:cod#sup] {
  def dom : category[dom]
  def cod : category[cod]
  def apply[
    a>:dom#inf<:dom#sup,
    b>:dom#inf<:dom#sup,
    c>:dom#inf<:dom#sup,
    d>:dom#inf<:dom#sup
  ](f: dom#dihom[a,b,c,d]): cod#dihom[f[a],f[b],f[c],f[d]]

  def dual : functor[hom.set.dual[dom], hom.set.dual[cod], f] = functor.op[dom,cod,f](this)
  def compose[pre<:hom.set,g[+_>:pre#inf<:pre#sup]>:dom#inf<:dom#sup](
    that: functor[pre,dom,g]
  ) = functor.composition[pre,dom,cod,f,g](this,that)
}

object functor {
  import equality._
  import hom.set._

  def duality[
    dom<:hom.set,
    cod<:hom.set,
    f[+_>:dom#inf<:dom#sup]>:cod#inf<:cod#sup
  ]:functor[dom,cod,f] === functor[dual[dual[dom]],dual[dual[cod]],f] = refl[functor[dom,cod,f]].asInstanceOf[
    functor[dom,cod,f] === functor[dual[dual[dom]],dual[dual[cod]],f]
  ]

  trait op[dom<:hom.set, cod<:hom.set, f[+_>:dom#inf<:dom#sup]>:cod#inf<:cod#sup] extends functor[hom.set.dual[dom], hom.set.dual[cod], f] {
    def dom : category[hom.set.dual[dom]] = dual.dom.dual
    def cod : category[hom.set.dual[cod]] = dual.cod.dual
    def apply[
      a>:dom#inf<:dom#sup,
      b>:dom#inf<:dom#sup,
      c>:dom#inf<:dom#sup,
      d>:dom#inf<:dom#sup
    ](f: dom#dihom[c,d,a,b]): cod#dihom[f[c],f[d],f[a],f[b]] = dual[c,d,a,b](f)
  }

  object op {
    def apply[dom<:hom.set,cod<:hom.set, f[+_>:dom#inf<:dom#sup]>:cod#inf<:cod#sup](f: functor[dom,cod,f]) : op[dom,cod,f] = new op[dom,cod,f] { 
      override def dual : functor[dual[dual[dom]], dual[dual[cod]], f] = duality[dom,cod,f](f)
    }
  }

  trait composition[
    a<:hom.set,
    b<:hom.set,
    c<:hom.set,
    f[+_>:b#inf<:b#sup]>:c#inf<:c#sup,
    g[+_>:a#inf<:a#sup]>:b#inf<:b#sup
  ] extends functor[a,c,({type λ[+x>:a#inf<:a#sup] = f[g[x]]})#λ] {
    protected def f : functor[b,c,f]
    protected def g : functor[a,b,g]
    def dom : category[a] = g.dom
    def cod : category[c] = f.cod
    def apply[
      A>:a#inf<:a#sup, 
      B>:a#inf<:a#sup,
      C>:a#inf<:a#sup,
      D>:a#inf<:a#sup
    ](h: a#dihom[A,B,C,D]): c#dihom[f[g[A]],f[g[B]],f[g[C]],f[g[D]]] = f(g(h))
  }

  object composition { 
    def apply[
      a<:hom.set,
      b<:hom.set,
      c<:hom.set,
      f[+_>:b#inf<:b#sup]>:c#inf<:c#sup,
      g[+_>:a#inf<:a#sup]>:b#inf<:b#sup
    ](
      F : functor[b,c,f],
      G : functor[a,b,g]
    ) : composition[a,b,c,f,g] = 
    new composition[a,b,c,f,g] {
      protected def f : functor[b,c,f] = F 
      protected def g : functor[a,b,g] = G
    }
  }
}
