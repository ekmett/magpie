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

    type product[x<:set,y<:set] = set { 
      type inf = phantom.product[x#inf,y#inf]
      type sup = phantom.product[x#sup,y#sup]
      type hom[a>:inf<:sup,b>:inf<:sup] = hom.product[x,y,a,b]
    }
  }

  case class product[
    x<:hom.set,
    y<:hom.set,
    a>:phantom.product[x#inf,y#inf]<:phantom.product[x#sup,y#sup],
    b>:phantom.product[x#inf,y#inf]<:phantom.product[x#sup,y#sup]
  ](
    _1: x#hom[a#_1,b#_1],
    _2: y#hom[a#_2,b#_2]
  ) extends phantom.product[x#hom[a#_1,b#_1],y#hom[a#_2,b#_2]]
}
