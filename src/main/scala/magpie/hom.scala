package magpie

/** currently these play the roles of both hom-classes and hom-sets */
object hom { 
//  import equality._
  /** hom-sets are modeled as a range of types. 
    * sealed to ensure the validity of the duality laws 
    * and that it is never actually constructed
    */
  sealed trait set { self => 
    type obinf
    type obsup >: obinf
    type ob[-_>:obinf<:obsup,+_>:obinf<:obsup]
    type inf = ob[obsup,obinf]
    type sup = ob[obinf,obsup]
    type hom[-_>:inf<:sup,+_>:inf<:sup] 
  }

  object set {
    /** the dual of a hom-set is a hom-set */
    type dual[h<:set] = set { 
			type obinf = h#obinf
      type obsup = h#obsup
      type ob[-a>:obinf<:obsup,+b>:obinf<:obsup] = h#ob[b,a]
      type inf = h#inf
      type sup = h#sup
      type hom[-a>:inf<:sup,+b>:inf<:sup] = h#hom[b,a]
    }

    /** hom.set.of: convenient accessor to construct a particular hom.set */
    type of[l, h>:l, o[-_>:l<:h,+_>:l<:h], c[-_>:o[h,l]<:o[l,h],+_>:o[h,l]<:o[l,h]]] = set {
      type obinf = l
      type obsup = h
      type ob[-a>:obinf<:obsup,+b>:obinf<:obsup] = o[a,b]
      type inf = ob[obsup,obinf]
      type sup = ob[obinf,obsup]
      type hom[-a>:inf<:sup,+b>:inf<:sup] = c[a,b]
    }

    /** hom.set.singleton: creates a hom-set that consists of a single type */
    type singleton[z] = of[z,z,({type λ[-x>:z<:z,+y>:z<:z]=z})#λ,({type λ[-x>:z<:z,+y>:z<:z] = z})#λ]

    /** hom.set.duality: hack to witness the equality of a hom-set to its dual dual */
    def duality[h<:set] : equality[Nothing,set,h,dual[dual[h]]] = 
      equality.refl[h].asInstanceOf[equality[Nothing,set,h,dual[dual[h]]]]

    /** hom.set.product: the product of two hom-sets */
    type product[x<:set,y<:set] = set { 
      type obinf = typed.product[x#obinf,y#obinf]
      type obsup = typed.product[x#obsup,y#obsup]
      type ob[-a>:obinf<:obsup,+b>:obinf<:obsup] = typed.product[x#ob [a#_1,b#_1], y#ob [a#_2,b#_2]]

      // busted:
      // type inf = ob[obsup,obinf]// -- compiler bug. see reasoning
      // type sup = ob[obinf,obsup]

      // the full expansion doesn't work at all:
      // type inf = typed.product[x#ob[x#obsup,x#obinf], y#ob[y#obsup, y#obinf]]
      // type sup = typed.product[x#ob[x#obinf,x#obsup], y#ob[y#obinf, y#obsup]]

      // works until instantiation:
      type inf = typed.product[x#inf,y#inf]
      type sup = typed.product[x#sup,y#sup]
      type hom[-a>:inf<:sup,+b>:inf<:sup] = typed.product[x#hom[a#_1,b#_1], y#hom[a#_2,b#_2]]
    }
    object product { 
      def hom[
        x<:set,y<:set,
        a>:typed.product[x#inf,y#inf]<:typed.product[x#sup,y#sup],
        b>:typed.product[x#inf,y#inf]<:typed.product[x#sup,y#sup]
      ] (
        l: x#hom[a#_1,b#_1],
        r: y#hom[a#_2,b#_2]
      ) = typed.product[x#hom[a#_1,b#_1], y#hom[a#_2,b#_2]](l,r)
      /** hom.set.product.duality: another bald-faced assertion about duality. */
      def duality[x <: set, y <: set] : subtype[Nothing,set,product[dual[x],dual[y]],dual[product[x,y]]] = 
        subtype.refl[product[dual[x],dual[y]]].asInstanceOf[subtype[Nothing,set, product[dual[x],dual[y]], dual[product[x,y]]]]
    }
  }
}
