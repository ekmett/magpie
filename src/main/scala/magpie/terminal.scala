package magpie

object terminal { 
  // an element 1 with !: x -> 1 forall x in c
  trait element[h<:hom.set] { // object 
    type T >: h#inf <: h#sup
    def category : category[h]
    def fini[x>:h#inf<:h#sup] : h#hom[x,T]
    def dual: initial.element[hom.set.dual[h]]
  }
}
// strict.terminal.element: any morphism T -> x must be an isomorphism

object initial { 
  // an element 0 with !: 0 -> x forall x in c
  trait element[h<:hom.set] { 
    type I >: h#inf <: h#sup
    def category: category[h]
    def init[x>:h#inf<:h#sup] : h#hom[I,x]
    def dual: terminal.element[hom.set.dual[h]]
  }
}
// strict.initial.element: any morphism x -> I must be an isomorphism


object zero { 
  // a category with a zero element is called a pointed category
  trait element[h<:hom.set] extends terminal.element[h] with initial.element[h] {
    type Z >: h#inf <: h#sup
    type I = Z
    type T = Z
    def dual: zero.element[hom.set.dual[h]]
  }
}

// strict.zero.element: the category has exactly one morphism
