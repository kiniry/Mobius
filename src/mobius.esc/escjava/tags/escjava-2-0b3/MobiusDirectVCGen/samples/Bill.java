             abstract class Bill {

               private int sum;
               //@ invariant sum >= 0;

               //@ ensures \result <= x;
               abstract int round_cost(int x) throws Exception;

               //@ requires n > 0;
               //@ ensures sum <= \old(sum) + n * (n + 1) / 2;
               public boolean produce_bill(int n) {
                 int i;
                 try{
                   //@ loop_invariant i <= n + 1 && sum <= \old(sum) + (i - 1) * i / 2;
                   for (i = 1; i <= n; i++) {
                     this.sum = this.sum + round_cost(i);
                   }
                   return true;
                 } catch (Exception e) {
                   return false;
                 }
               }
             }
