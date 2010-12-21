package magpie

/** currently these play the roles of both hom-classes and hom-sets */
object hom { 

  sealed trait set { self => 
    type inf
    type sup >: inf
    type dihom[-_>:inf<:sup,+_>:inf<:sup,-_>:inf<:sup,+_>:inf<:sup]
  }

  type C[+t<:set,a>:t#inf<:t#sup,b>:t#inf<:t#sup] = t#dihom[a,a,b,b]

  object set {
    /** the dual of a hom-set is a hom-set */
    type dual[h<:set] = set { 
      type inf = h#inf
      type sup = h#sup
      type dihom[-a>:inf<:sup,+b>:inf<:sup,-c>:inf<:sup,+d>:inf<:sup] = h#dihom[c,d,a,b]
    }

    /** hom.set.of: convenient accessor to construct a particular hom.set */
    type of[l, h>:l, C[-_>:l<:h,+_>:l<:h,-_>:l<:h,+_>:l<:h]] = set {
      type inf = l
      type sup = h
      type dihom[-a>:inf<:sup,+b>:inf<:sup,-c>:inf<:sup,+d>:inf<:sup] = C[a,b,c,d]
    }

    /** hom.set.singleton: creates a hom-set that consists of a single type */
    type singleton[z] = of[z,z,({type λ[-a>:z<:z,+b>:z<:z,-c>:z<:z,+d>:z<:z] = z})#λ]

    type scala = set { 
      type inf = Nothing
      type sup = Any
      type dihom[-a>:inf<:sup,+b>:inf<:sup,-c>:inf<:sup,+d>:inf<:sup] = a => d
    }

    /** hom.set.duality: hack to witness the equality of a hom-set to its dual dual */
    def duality[h<:set] : equality[Nothing,set,h,dual[dual[h]]] = 
      equality.refl[h].asInstanceOf[equality[Nothing,set,h,dual[dual[h]]]]

    /** hom.set.product: the product of two hom-sets */
    type product[x<:set,y<:set] = set { 
      type inf = typed.product[x#inf,y#inf]
      type sup = typed.product[x#sup,y#sup]
      type dihom[-a>:inf<:sup,+b>:inf<:sup,-c>:inf<:sup,+d>:inf<:sup] = typed.product[x#dihom[a#_1,b#_1,c#_1,d#_1], y#dihom[a#_2,b#_2,c#_2,d#_2]]
    }

    object product { 
      def hom[
        x<:set,y<:set,
        a>:typed.product[x#inf,y#inf]<:typed.product[x#sup,y#sup],
        b>:typed.product[x#inf,y#inf]<:typed.product[x#sup,y#sup]
      ] (
        l: C[x,a#_1,b#_1],
        r: C[y,a#_2,b#_2]
      ) = typed.product[C[x,a#_1,b#_1], C[y,a#_2,b#_2]](l,r)
      /** hom.set.product.duality: another bald-faced assertion about duality. */
      def duality[x <: set, y <: set] : subtype[Nothing,set,product[dual[x],dual[y]],dual[product[x,y]]] = 
        subtype.refl[product[dual[x],dual[y]]].asInstanceOf[subtype[Nothing,set, product[dual[x],dual[y]], dual[product[x,y]]]]
    }
  }
}
