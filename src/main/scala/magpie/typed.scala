package magpie

object typed { 
  case class product[+x,+y](_1: x, _2: y) 
     extends scala.Product2[x,y] with phantom.product[x,y] {

    override def toString() = "(" + _1 + "," + _2 + ")"

    def swap: product[y,x] = product(_2,_1)
  }

  object product { 
    implicit def toTypedProduct[x,y](p: (x,y)): product[x,y] = product(p._1,p._2)
    implicit def fromTypedProduct[x,y](p: product[x,y]): (x,y) = (p._1, p._2)
  }
}
