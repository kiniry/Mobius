public class A {
  int val ; 
  A next;

  A m(A list ) {
   while (list.next != null ) {
     list = list.next;
   }
//   A copy = new A();
//   copy.val = list.val;
   return new A();
  } 
}

