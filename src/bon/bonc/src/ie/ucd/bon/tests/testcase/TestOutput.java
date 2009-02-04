/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests.testcase;

import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.source.SourceLocation;

import java.io.File;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.Vector;

public class TestOutput {

  private static final String[] PACKAGES = { "ie.ucd.bon.errorreporting", "ie.ucd.bon.parser.errors", "ie.ucd.bon.typechecker.errors", "ie.ucd.bon.typechecker.informal", "ie.ucd.bon.typechecker.informal.errors" };

  private String errorType;
  private final Collection<String> extraParams;
  
  public TestOutput() {
    extraParams = new Vector<String>();
  }

  public void setErrorType(String errorType) {
    this.errorType = errorType;
  }
  
  public void addExtraParam(String param) {
    extraParams.add(param);
  }

  
  public BONProblem getProblem() {
    Class c = null;

    for (String pack : PACKAGES) {
      try {
        c = Class.forName(pack + "." + errorType);
        //System.out.println("Matched " + pack + "." + errorType);
        break;
      } catch (ClassNotFoundException cnfe) {
        //System.out.println("Did not match " + pack + "." + errorType);
        //Do nothing
      }
    }

    if (c == null) {
      System.out.println("Error: Invalid Error type " + errorType);
      return null;
    }

    Constructor[] cons = c.getConstructors();

    //Find the constructor which requires the most arguments and use it.
    int longestConstructorIndex = 0;
    int longestConstructorSize = 0;    
    for (int i=0; i < cons.length; i++) {
      if (cons[i].getParameterTypes().length > longestConstructorSize) {
        //Avoid constructors with collections...
        if (Arrays.asList(cons[i].getParameterTypes()).contains(Collection.class)) {
          continue;
        }
        longestConstructorIndex = i;
        longestConstructorSize = cons[i].getParameterTypes().length;
      }
    }    
    Constructor constructor = cons[longestConstructorIndex];
    
    Class[] paramTypes = constructor.getParameterTypes();

    if (paramTypes.length != extraParams.size()) {
      if (paramTypes[0].equals(SourceLocation.class) && paramTypes.length == extraParams.size() - 2) {
        //It's ok
      } else {
        System.out.println("Invalid arguments for constructor of " + errorType);
        return null;
      }
    }

    Object[] args = new Object[paramTypes.length];

    Iterator<String> iterator = extraParams.iterator();
    for (int i=0; i < args.length; i++) {

      if (paramTypes[i].equals(String.class)) {
        String s = iterator.next();
        if (s.charAt(0) == '"') {
          //Remove surrounding ""
          s = s.substring(1, s.length()-1);
        }
        args[i] = s;
      } else if (paramTypes[i].equals(int.class)) {
        args[i] = Integer.parseInt(iterator.next());
      } else if (paramTypes[i].equals(boolean.class)) {
        args[i] = Boolean.parseBoolean(iterator.next());
      } else if (paramTypes[i].equals(File.class)) {
        args[i] = new File(iterator.next());
      } else if (paramTypes[i].equals(SourceLocation.class)) {
        args[i] = new SourceLocation(new File(iterator.next()), Integer.parseInt(iterator.next()), Integer.parseInt(iterator.next()), -1, -1);
      }
    }

    try {
      Object instance = constructor.newInstance(args);
      //((BONProblem)instance).print(System.out);
      return (BONProblem)instance;
    } catch (IllegalArgumentException e) {
      //We give it incorrect arguments
    } catch (InstantiationException e) {
      //Should not happen, all Error constructors are public
    } catch (IllegalAccessException e) {
      //Should not happen
    } catch (InvocationTargetException e) {
      //Should not happen, no constructors are (explicitly) thrown
    }

    return null;
  }
  
}
