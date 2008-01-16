class Node/*#{ghost Object g}*/ {
  public volatile Node/*#{g}*/ next;
  public int x /*#guarded_by g*/;
  
  Node(Node/*#{g}*/ next, int x) /*#no_warn*/ {
    /*#holds g*/
    this.next = next;
    this.x = x;
  }
}

public class Main {
  public static void main(String[] args) {
    new Main().go();
  }

  private volatile Node/*#{this}*/ head = null;

  private synchronized void addNode(int x) {
    head = new Node/*#{this}*/(head, x);
  }

  private void go() {
    addNode(1);
    addNode(2);
    synchronized(this) {
      System.out.println(head.next.x);
    }
  }
}
