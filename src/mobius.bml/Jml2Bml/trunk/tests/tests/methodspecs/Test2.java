package tests.methodspecs;


public class Test2 {
  private static Test2 instance = null;

  //@ ensures \result != null;
  public static Test2 getInstance() {
    if (instance == null)
      instance = new Test2();
    return instance;
  }

  //@ requires param != null;
  public static Test2 getInstance(String param) {
    return instance;
  }
}
