package test;

public class Toto {

	  
	/*@ 
	  @ public behavior
	  @	forall int i; 
      @   requires 0 <= i && size < MAX_SIZE; 
      @   assignable size if elem >= 0, elems[*] if elem >= 0; 
      @   ensures \old(elem >= 0) 
      @        && \result == size && size == \old(size) + 1 
      @        && (\forall int i; (0 <= i && i < \old(size)) ==> elems[i] == \old(elems[i])) 
      @        && elems[size-1] == elem;
      @   signals (Exception e) \old(elem < 0);
      @*/ 
  public int push(int elem) throws  Exception{ 
      if (elem >= 0) { 
          elems[size++] = elem; 
          return size; 
      } 
      else { 
          throw new Exception(); 
      } 
  }	 
	 public static final int MAX_SIZE = 10; 
	  
	  private /*@ spec_public @*/ int size = 0; 
	  
	  private /*@ non_null spec_public @*/ int[] elems = new int[MAX_SIZE];        
 
}


