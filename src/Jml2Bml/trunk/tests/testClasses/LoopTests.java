package testClasses;

public class LoopTests {
  public void test1() {
    int j = 0;
    for (int i = 0; i < 2; i++) {
      j++;
    }
  }

  public void test2() {
    int j = 0;
    int[] tab = new int[17];
    for (int i : tab) {
      j++;
    }
  }

  public void test3() {
    int j = 0;
    for (;;) { //while true
      j++;
    }
  }

  public void test4() {
    int j = 0;
    while (true) {
      j++;
    }
  }

  public void test5() {
    int j = 0;
    while (j < 15) {
      j++;
    }
  }

  public void test6() {
    int j = 0;
    do {
      j++;
    } while (true);
  }

  public void test7() {
    int j = 0;
    do {
      j++;
    } while (j < 17);
  }

  public void test8() {
    int k = 0;
    for (int i = 0; i < 13; i++)
      for (int j = 0; j < 15; j++)
        k++;
  }

  public void testJF_ELSE() {
    int j = 0;
    if (j < 0) {
      j = 17;
    } else {
      do {
        j++;
      } while (j < 12);
    }
  }

  public void test9() {
    int j = 0;
    while (true) {
      j++;
      if (j > 12)
        break;
    }
  }
  /*
   public void test10() {
     int j=0;
     while(true) {
       j++;
       if (j<13)
         continue;
     }
   }
   public void test11() {
     int i=0;
     outer :
     while (true) {
       i++;
       for(int j=0; j<13; j++) {
         if (j>12 && i<j)
           break outer;
       }
     }
   }

   public void test12() {
     for(int i=0; i<100; i++) {
       inner: for(int j=0; j<100; j++)
         for (int k=0; k<100; k++)
           if (i>12 && j>12 && k>12)
             break inner;
       if (i<13)
         break;
     }
   }
  public void test15() {
   a: for (int i = 0; i < 12; i++)
     b: for (int j = 0; j < 12; j++)
       c: for (int k = 0; k < 12; k++) {
         for (int l = 0; l < 12; l++)
           if (k < l)
             break b;
         if (j > k)
           break a;
       }
  }

  /*
  public void test13() {
   try {
     for (int i=0; i<12; i++)
       if (i>10)
         throw new Exception();
   } catch (Exception e) {
     for (int j=0; j<12; j++)
       if (j>10)
         throw new RuntimeException();
   }
  }
  
  public void test14() {
   try {
     for (int i=0; i<12; i++)
       if (i>10)
         throw new Exception();
   } catch (Exception e) {
     for (int j=0; j<12; j++)
       if (j>10)
         break;
   } finally {
     int j=0;
     while(j<12)
       j++;
   }
     
  }*/
}
