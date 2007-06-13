package a;

public class Main {
  static {
    System.setSecurityManager(new SecurityManager() {
      public void checkPackageAccess(String target) {
        super.checkPackageAccess(target);
        if(target.equals("b"))
          throw new SecurityException("That is true");
      }
    });
  }
  /**
   * @param args
   */
  public static void main(String[] args) {
    System.out.println("The following line will throw an exception");
    b.A a = new b.A();
  }

}
