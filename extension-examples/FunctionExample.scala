object FunctionExample {
  def foo(a: Int, b: Int = 1): Int = {
    10*a + b
  }

  Std.printInt(foo(0)); //1
  Std.printInt(foo(0,0)); //0
  Std.printInt(foo(b=0, a=2)) //20
}
