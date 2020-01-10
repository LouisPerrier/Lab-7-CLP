object ClassExample {
  abstract class Foo
  case class Bar(x: Int, y: Int, z: Int = 0, b: Boolean = false) extends Foo

  def foobar(x: Int, y: Int, z: Int = 0, b: Boolean = false): Int = {
    if (b==true) {42} else {100*x + 10*y + z}
  }
  val f1: Foo = Bar(0, 1, z=5);
  f1 match {
    case Bar(x,y,z,b) => Std.printInt(foobar(x,y,z,b)) //15
  };

  val f2: Foo = Bar(0, 0, b=true);
  f2 match {
    case Bar(x,y,z,b) => Std.printInt(foobar(x,y,z,b)) //42
  };

  val f3: Foo = Bar(z=1, y=2, x=3);
  f3 match {
    case Bar(x,y,z,b) => Std.printInt(foobar(x,y,z,b)) //321
  }
}
  