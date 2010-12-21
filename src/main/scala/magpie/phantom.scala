package magpie

object phantom { 
  trait product[+x,+y] { 
    type _1 = x
    type _2 = y
  }
  trait morphism[-x,+y] { 
    type _1 = x
    type _2 = y
  }
}
