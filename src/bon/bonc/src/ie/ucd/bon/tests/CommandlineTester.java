/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.Main;
import ie.ucd.commandline.options.InvalidOptionsSetException;

public class CommandlineTester {

  public static void main(String[] args) throws InvalidOptionsSetException {
    
    
    String[] tests = { 
        "--help hjkhjk",                  //Help, even with other invalid options
        "-pp test.bon",                   //Print with invalid file
        "-pp -tc ../test/classchart",     //Valid
        "-pp -tc ../test/clusterchart"    //Valid
    };
    
    
    for (String s : tests) {
      System.out.println("Testing with arguments: " + s);
      if (s.equals("")) {
        Main.main(new String[0]);
      } else {
        Main.main(s.split("\\s+"));
      }
    }
    

  }

}
