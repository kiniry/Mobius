package tests.methodspecs;

public class Test1 {
  private static Test1 instance = null;

  //@ ensures \result != null;
  public static Test1 getInstance() {
    if (instance == null)
      instance = new Test1();
    return instance;
  }
}
