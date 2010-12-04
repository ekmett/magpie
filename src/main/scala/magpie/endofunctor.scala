package magpie

trait endofunctor[carrier<:hom.set,f[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup] extends functor[carrier,carrier,f] { 
  def carrier : category[carrier]
  override def dom : category[carrier] = carrier
  override def cod : category[carrier] = carrier

  override def dual : endofunctor[hom.set.dual[carrier], f] = endofunctor.op[carrier,f](this)

  /*overload*/ def compose[g[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup](
    that: endofunctor[carrier,g]
  ) = endofunctor.composition[carrier,f,g](this,that)
}

object endofunctor { 
  import equality._
  import hom.set._
  def duality[
    carrier<:hom.set, 
    f[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup
  ]:endofunctor[carrier,f] === endofunctor[dual[dual[carrier]],f] = refl[endofunctor[carrier,f]].asInstanceOf[
    endofunctor[carrier,f] === endofunctor[dual[dual[carrier]],f]
  ]

  trait op[carrier<:hom.set,f[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup] extends 
	functor.op[carrier, carrier, f] with endofunctor[hom.set.dual[carrier], f] {
    def carrier : category[hom.set.dual[carrier]] = dual.carrier.dual
  }

  object op {
    def apply[
      carrier<:hom.set,
      f[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup
    ](
      f: endofunctor[carrier,f]
    ): op[carrier,f] = new op[carrier,f] { 
      override def dual : endofunctor[hom.set.dual[hom.set.dual[carrier]],f] = witness(duality[carrier,f])(f)
    }
  }

  trait composition[
    carrier<:hom.set,
    f[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup,
    g[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup
  ] extends functor.composition[carrier,carrier,carrier,f,g] 
       with endofunctor[carrier,({type λ[x>:carrier#inf<:carrier#sup] = f[g[x]]})#λ] {
    def carrier : category[carrier] = f.dom
    override def dom : category[carrier] = carrier
    override def cod : category[carrier] = carrier
    protected def f : endofunctor[carrier, f]
    protected def g : endofunctor[carrier, g]
  }

  object composition { 
    def apply[
      carrier<:hom.set,
      f[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup,
      g[_>:carrier#inf<:carrier#sup]>:carrier#inf<:carrier#sup
    ](
      F : endofunctor[carrier,f],
      G : endofunctor[carrier,g]
    ) : composition[carrier,f,g] = 
    new composition[carrier,f,g] {
      protected def f : endofunctor[carrier,f] = F 
      protected def g : endofunctor[carrier,g] = G
    }
  }

  def id[dom<:hom.set](implicit c: category[dom]): endofunctor[dom, ({type λ[x>:dom#inf<:dom#sup]=x})#λ] =
                                               new endofunctor[dom, ({type λ[x>:dom#inf<:dom#sup]=x})#λ] {
    def carrier : category[dom] = c
    def apply[a>:dom#inf<:dom#sup, b>:dom#inf<:dom#sup](f: dom#hom[a,b]): dom#hom[a,b] = f
  }
}
