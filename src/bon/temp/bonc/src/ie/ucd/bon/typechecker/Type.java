/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import java.util.Collection;
import java.util.Map;
import java.util.Vector;

public class Type {

  private final String inEntirety;
  private final String firstBit;
  private final Collection<Type> generics;
  
  public Type(String t, Map<String,Type> existingTypes) {
    //System.out.println("Constructing type: " + t);
    this.inEntirety = t;
    generics = new Vector<Type>();
    
    int p = t.indexOf("[");
    if (p == -1) {
      this.firstBit = t;
    } else {
      this.firstBit = t.substring(0, p);
      processRest(t.substring(p+1, t.length()-1), existingTypes);
    }    
    existingTypes.put(t, this);
  }
  
  private void processRest(String text, Map<String,Type> existingTypes) {

    if (text.charAt(0) == ',') {
      text = text.substring(1);
    }
    
    int pComma = text.indexOf(",");
    int pBracket = text.indexOf("[");
    
    String firstGeneric;
    if (pComma == -1 && pBracket == -1) {
      firstGeneric = text;      
    } else if (pComma == -1 || pBracket < pComma) {
      int pClosing = findMatchingClosingBracketPosition(text, pBracket);
      firstGeneric = text.substring(0, pClosing + 1);
    } else {
      firstGeneric = text.substring(0, pComma);      
    }
    
    Type t = existingTypes.get(firstGeneric);
    if (t == null) {
      t = new Type(firstGeneric, existingTypes);
      existingTypes.put(text, t);
    }     
    generics.add(t);

    if (firstGeneric.length() < text.length()) {
      processRest(text.substring(firstGeneric.length()+1), existingTypes);
    }
  }
  
  private static int findMatchingClosingBracketPosition(String t, int start) {
    int nestedLevel = 1;
    for (int i=start+1; i < t.length(); i++) {
      switch(t.charAt(i)) {
        case '[':
          nestedLevel++;
          break;
        case ']':
          nestedLevel--;
          if (nestedLevel == 0) {
            return i;
          }
          break;
      }
    }
    return -1; //Shouldn't happen for a properly formatted string
  }
  
  public static void main(String[] args) {
    String[] tests = { "[]", "[a[b]],acc", "[ab[ac[ab],ac],ac],add,abb[ab[o]]"};
    
    for (String s : tests) {
      System.out.println("Testing: " + s);
      int match = findMatchingClosingBracketPosition(s, 0);
      System.out.println("Match = " + match);
    }
  }

  public boolean equals(Object obj) {
    if (obj instanceof Type) {
      return inEntirety.equals(((Type)obj).inEntirety);
    } else {
      return false;
    }
  }

  public int hashCode() {
    return inEntirety.hashCode();
  }

  public String toString() {
    return inEntirety;
  }
  
  public boolean hasGenerics() {
    return generics.size() > 0;
  }

  public String getNonGenericType() {
    return firstBit;
  }
  
  
  
  
}
