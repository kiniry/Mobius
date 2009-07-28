class A {} // should not need an explicit thread_shared annotation

public class C {
  private A a /*# guarded_by this */;
}
