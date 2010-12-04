package magpie

object typed { 
  case class product[+x,+y](_1: x, _2: y) extends scala.Product2[x,y] { 
    type _1 = x
    type _2 = y
  }
  object product { 
    implicit def to[x,y](p: (x,y)): product[x,y] = product(p._1,p._2)
    implicit def from[x,y](p: product[x,y]): (x,y) = (p._1, p._2)
  }

}
