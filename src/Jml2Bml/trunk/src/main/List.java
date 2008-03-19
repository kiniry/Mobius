package main;

public class List {

  private Object[] list;

  /*@  requires list != null;
        @ ensures \result ==(\exists int i;
    @ 0 <= i && i < list.length &&
    @ \old(list[i]) == o1 && list[i] == o2);
    @*/
  public boolean replace(Object o1, Object o2) {
    /*@
      @ loop_invariant i <= list.length && i >=0 && (\forall int k;0 <= k && k < i ==>
      @     list[k] != o1);
      @ decreases list.length - i;
      @*/
    for (int i = 0; i < list.length; i++) {
      if (list[i] == o1) { 
        list[i] = o2;
        return true;
      }
    }
    return false;
  }
}

