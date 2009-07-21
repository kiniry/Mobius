/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.tests.testcase.TestCase;

import java.util.Collection;
import java.util.Vector;

import org.antlr.runtime.Parser;
import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.TokenStream;

public abstract class AbstractTesterParser extends Parser {

  private final Collection<TestCase> testCases;
  
  public AbstractTesterParser(TokenStream input, RecognizerSharedState state) {
    super(input, state);
    testCases = new Vector<TestCase>();
  }

  protected void addTestCase(TestCase testCase) {
    testCases.add(testCase);    
  }
  
  public Collection<TestCase> getTestCases() {
    return testCases;
  }
  
}
