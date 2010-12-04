package magpie

/** currently these play the roles of both hom-classes and hom-sets */
object hom { 
  import equality._
  /** hom-sets are modeled as a range of types. 
    * sealed to ensure the validity of the duality laws 
    * and that it is never actually constructed
    */
  sealed trait set { self => 
    type inf
    type sup >: inf
    type hom[_>:inf<:sup,_>:inf<:sup] 
  }

  object set {
    /** the dual of a hom-set is a hom-set */
    type dual[h<:set] = set { 
      type inf = h#inf
      type sup = h#sup
      type hom[a>:inf<:sup,b>:inf<:sup] = h#hom[b,a]
    }

    /** hom.set.of: convenient accessor to construct a particular hom.set */
    type of[l,h>:l,c[_>:l<:h,_>:l<:h]] = set {
      type inf = l
      type sup = h
      type hom[x>:l<:h,y>:l<:h] = c[x,y]
    }

    /** hom.set.singleton: creates a hom-set that consists of a single type */
    type singleton[z] = of[z,z,({type λ[x>:z<:z,y>:z<:z] = z})#λ]

    /** hom.set.duality: hack to witness the equality of a hom-set to its dual dual */
    def duality[h<:set] : equality[Nothing,set,h,dual[dual[h]]] = 
      equality.refl[h].asInstanceOf[equality[Nothing,set,h,dual[dual[h]]]]

    /** hom.set.product: the product of two hom-sets */
    type product[x<:set,y<:set] = set { 
      type inf = typed.product[x#inf,y#inf]
      type sup = typed.product[x#sup,y#sup]
      type hom[a>:inf<:sup,b>:inf<:sup] = typed.product[x#hom[a#_1,b#_1], y#hom[a#_2,b#_2]]
    }
    object product { 
      /** hom.set.product.duality: another bald-faced assertion about duality. */
      def duality[x <: set, y <: set] : subtype[Nothing,set,product[dual[x],dual[y]],dual[product[x,y]]] = 
        subtype.refl[product[dual[x],dual[y]]].asInstanceOf[subtype[Nothing,set, product[dual[x],dual[y]], dual[product[x,y]]]]
    }
  }
}
