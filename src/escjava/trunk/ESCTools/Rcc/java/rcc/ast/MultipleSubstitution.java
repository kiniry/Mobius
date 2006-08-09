/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.ast;

import javafe.util.Assert;
import javafe.util.Location;
import rcc.ast.SubstitutionVec;

import javafe.ast.*;


public class MultipleSubstitution {
  SubstitutionVec substitutions;
  EqualsASTNoDecl equalityTester;
  
  public  MultipleSubstitution(SubstitutionVec s) {
    equalityTester = new EqualsAST();
    substitutions = s;
  }
  
  
  public  MultipleSubstitution(SubstitutionVec s, EqualsASTNoDecl e) {
    equalityTester = e;
    substitutions = s;
  }
  
  public  MultipleSubstitution() {
    this(SubstitutionVec.make());
  }
  
  public String  toString() {
    return substitutions.toString();
  }
  
  public ASTNode  substitute(ASTNode a) {
    int i;
    for (i = 0; i < substitutions.size(); i++) {
      Substitution s = substitutions.elementAt(i);
      if (equalityTester.equals(s.match,a)) {
        //System.out.println(a);
        //new Exception().printStackTrace(System.out);
        return s.replace;
      }
    }
    return null;
  }
  
}

