package magpie

trait equality[-l,+h>:l,a>:l<:h,b>:l<:h] {
  def subst[f[_>:l<:h]](a : f[a]) : f[b]
  final def compose[l2<:l,h2>:h,c>:l2<:h2](that: equality[l2,h2,c,a]) : equality[l2,h2,c,b] = equality.trans[l2,h2,c,a,b](this,that)
  final def andThen[l2<:l,h2>:h,c>:l2<:h2](that: equality[l2,h2,b,c]) : equality[l2,h2,a,c] = equality.trans[l2,h2,a,b,c](that,this)
  final def inverse : equality[l,h,b,a] = equality.symm[l,h,a,b](this)
  final def lift[lt,ht>:lt,t[_>:l<:h]>:lt<:ht] : equality[lt,ht,t[a],t[b]] = equality.lift[l,lt,h,ht,t,a,b](this)
}

object equality{ 
  type ===[a,b] = equality[Nothing,Any,a,b]

  /** equality is reflexive */
  def refl[a] : equality[a,a,a,a]= new equality[a,a,a,a] {
    def subst[f[_>:a<:a]](a : f[a]) : f[a] = a
  }

  /** equality is transitive */
  def trans[l,h>:l,a>:l<:h,b>:l<:h,c>:l<:h](
    f: equality[l,h,b,c],
    g: equality[l,h,a,b]
  )  : equality[l,h,a,c] =
    f.subst[({type λ[x>:l<:h]= equality[l,h,a,x]})#λ](g)

  /** equality is symmetric */
  def symm[l,h>:l,a>:l<:h,b>:l<:h](f: equality[l,h,a,b])  : equality[l,h,b,a] =
    f.subst[({type λ[x>:l<:h]=equality[l,h,x,a]})#λ](refl)

  /** equality can be witnessed by coercion */
  implicit def witness[a,b](f: a === b) : a => b =
    f.subst[({type λ[X]= a => X})#λ](identity[a])

  /** we can lift equality into type constructors */
  def lift[la,lt,ha>:la,ht>:lt,t[_>:la<:ha]>:lt<:ht,a>:la<:ha,a2>:la<:ha](
    a: equality[la,ha,a,a2]
  ) : equality[lt,ht,t[a],t[a2]] =
    a.subst[({type λ[x>:la<:ha] = equality[lt,ht,t[a],t[x]]})#λ](refl)
}
