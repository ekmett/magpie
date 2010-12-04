package magpie

/** currently these play the roles of both hom-classes and hom-sets */
object hom { 
  import equality._
  /** hom-sets are modeled as a range of types */
  trait set { self => 
    type inf
    type sup >: inf
    type hom[_>:inf<:sup,_>:inf<:sup] 
  }
  object set {
    type dual[h<:set] = set { 
      type inf = h#inf
      type sup = h#sup
      type hom[a>:inf<:sup,b>:inf<:sup] = h#hom[b,a]
    }
    /** hom.set.of makes it more convenient to construct a particular hom.set */
    type of[l,h>:l,c[_>:l<:h,_>:l<:h]] = set {
      type inf = l
      type sup = h
      type hom[x>:l<:h,y>:l<:h] = c[x,y]
    }

    /** creates a hom-set that consists of a single type */
    type singleton[z] = of[z,z,({type λ[x>:z<:z,y>:z<:z] = z})#λ]

    /** hack to witness the equality of a hom-set to its dual dual */
    def duality[h<:set] : equality[Nothing,set,h,dual[dual[h]]] = 
      refl[h].asInstanceOf[equality[Nothing,set,h,dual[dual[h]]]]
  }
}
