package magpie

trait subtype[-l,+h>:l,-a>:l<:h,+b>:l<:h] {
  def subst[f[-_>:l<:h]](p: f[b]) : f[a]
  def compose[l2<:l,h2>:h,c>:l2<:h2](that: subtype[l2,h2,c,a]) : subtype[l2,h2,c,b] = subtype.trans[l2,h2,c,a,b](this,that)
  def andThen[l2<:l,h2>:h,c>:l2<:h2](that: subtype[l2,h2,b,c]) : subtype[l2,h2,a,c] = subtype.trans[l2,h2,a,b,c](that,this)
  def colift[lt,ht>:lt,t[+_>:l<:h]>:lt<:ht]     : subtype[lt,ht,t[a],t[b]] = subtype.colift[l,lt,h,ht,t,a,b](this)
  def contralift[lt,ht>:lt,t[-_>:l<:h]>:lt<:ht] : subtype[lt,ht,t[b],t[a]] = subtype.contralift[l,lt,h,ht,t,a,b](this)
}

object subtype { 
  type <~<[-a,+b] = subtype[Nothing,Any,a,b] 
  type >~>[+b,-a] = subtype[Nothing,Any,a,b]

  /** reify an existing subtyping relationship as a subtype morphism */
  implicit def isa[a,b >: a] : subtype[a,b,a,b] = new subtype[a,b,a,b] {
    def subst[f[-_>:a<:b]](p: f[b]) : f[a] = p
  }

  /** witness a subtype by conversion */
  implicit def witness[a,b](lt: a <~< b) : a => b = 
    lt.subst[({type λ[-x] = x => b})#λ](identity)

  /** equality is reflexive, and subtyping is a supertype of equality */
  implicit def refl[a]: equality[a,a,a,a] = equality.refl[a]

  /** subtyping is transitive */ 
  def trans[l,h>:l,a>:l<:h,b>:l<:h,c>:l<:h](f: subtype[l,h,b,c], g: subtype[l,h,a,b]) : subtype[l,h,a,c] =
    g.subst[({type λ[-x>:l<:h] = subtype[l,h,x,c]})#λ](f)

  /** we can lift subtyping into type constructors covariantly */
  def colift[la,lt,ha>:la,ht>:lt,t[+_>:la<:ha]>:lt<:ht,a>:la<:ha,a2>:la<:ha](
    a: subtype[la,ha,a,a2]
  ) : subtype[lt,ht,t[a],t[a2]] =
    a.subst[({type λ[-x>:la<:ha] = subtype[lt,ht,t[x],t[a2]]})#λ](refl)

  /** we can lift subtyping into type constructors contravariantly */
  def contralift[la,lt,ha>:la,ht>:lt,t[-_>:la<:ha]>:lt<:ht,a>:la<:ha,a2>:la<:ha](
    a: subtype[la,ha,a,a2]
  ) : subtype[lt,ht,t[a2],t[a]] =
    a.subst[({type λ[-x>:la<:ha] = subtype[lt,ht,t[a2],t[x]]})#λ](refl)

  /** if a <: b and b >: a, and both lie between l and h, then they are equal and lie between l and h */
  def bracket[l,h>:l,a>:l<:h,b>:l<:h](
    ab : subtype[l,h,a,b],
    ba : subtype[l,h,b,a]
  ): equality[l,h,a,b] = equality.refl[a].asInstanceOf[equality[l,h,a,b]]
}
