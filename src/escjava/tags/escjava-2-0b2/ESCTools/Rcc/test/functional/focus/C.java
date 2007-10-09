public class C extends Object {

  /*# thread_shared */
  class CC/*#{ghost Object o}*/ {
  }

  CC/*#{this}*/ c /*# guarded_by this */;

  void f() {
    final C a = new C();
    CC/*#{a}*/ c = a.c;
  }
}
