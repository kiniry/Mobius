/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.Main;

public class CommandlineTester {

  public static void main(String[] args) {
    
    
    String[] tests = { 
        "--help hjkhjk",                  //Help, even with other invalid options
        "-pp test.bon",                   //Print with invalid file
        "-pp -tc ../test/classchart",     //Valid
        "-pp -tc ../test/clusterchart"    //Valid
    };
    
    
    for (String s : tests) {
      System.out.println("Testing with arguments: " + s);
      if (s.equals("")) {
        Main.main2(new String[0],false);
      } else {
        Main.main2(s.split("\\s+"),false);
      }
    }
    

  }

}
