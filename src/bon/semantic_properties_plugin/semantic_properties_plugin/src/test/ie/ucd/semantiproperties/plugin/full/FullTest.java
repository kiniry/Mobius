package ie.ucd.semantiproperties.plugin.full;


import ie.ucd.semanticproperties.plugin.api.LevelId;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertiesHandler;
import ie.ucd.semanticproperties.plugin.api.SemanticPropertyInstance;
import ie.ucd.semanticproperties.plugin.exceptions.IncompatibleSemanticPropertyInstancesException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidRefinementException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertySpecificationException;
import ie.ucd.semanticproperties.plugin.exceptions.InvalidSemanticPropertyUseException;
import ie.ucd.semanticproperties.plugin.exceptions.SemanticPropertyNotValidAtScopeException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownPropertyException;
import ie.ucd.semanticproperties.plugin.exceptions.UnknownVariableIdentifierException;

import java.io.File;
import java.io.IOException;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

public class FullTest {
  private static final String PATH = "resources/examples/junit/";
  private SemanticPropertiesHandler handler;
  
  @Before
  public void setUp() throws Exception {
    handler = new SemanticPropertiesHandler();
  }

  @After
  public void tearDown() throws Exception {
  }

  @Test(expected=IOException.class)
  public void invalidFile() throws InvalidSemanticPropertySpecificationException, IOException {
    handler.add(new File(PATH + "sdfasdfkjskdfjsa.yaml"));
  }  
  
  @Test public void addProperty() throws InvalidSemanticPropertySpecificationException, IOException {
    handler.add(new File(PATH + "../concurrency_full.yaml"));
  }
  
  @Test(expected=InvalidSemanticPropertySpecificationException.class)
  public void addGarbageProperty() throws InvalidSemanticPropertySpecificationException, IOException {
    handler.add(new File(PATH + "garbage.yaml"));
  }
  
  @Test(expected=InvalidSemanticPropertySpecificationException.class)
  public void addEmptyProperty() throws InvalidSemanticPropertySpecificationException, IOException {
    handler.add(new File(PATH + "empty.yaml"));
  }
  
  @Test(expected=InvalidSemanticPropertySpecificationException.class) 
  public void addSomewhatInvalidProperty() throws InvalidSemanticPropertySpecificationException, IOException {
    handler.add(new File(PATH + "invalidproperty.yaml"));
  }
  
  
  @Test 
  public void parsingTest1() throws InvalidSemanticPropertySpecificationException, IOException, UnknownPropertyException, InvalidSemanticPropertyUseException, SemanticPropertyNotValidAtScopeException {
    handler.add(new File(PATH + "../concurrency_full.yaml"));
    handler.parse("concurrency SEQUENTIAL", "concurrency", LevelId.BON_FORMAL);
    handler.parse("concurrency CONCURRENT", "concurrency", LevelId.BON_FORMAL);
  }
  
  @Test 
  public void parsingTest2() throws InvalidSemanticPropertySpecificationException, IOException, UnknownPropertyException, InvalidSemanticPropertyUseException, SemanticPropertyNotValidAtScopeException {
    handler.add(new File(PATH + "../concurrency_full.yaml"));
    handler.parse("concurrency TIMEOUT 5 Esadfadfxception", "concurrency", LevelId.BON_FORMAL);
    handler.parse("concurrency FAILURE a.Esadfadfxception", "concurrency", LevelId.BON_FORMAL);
  }
  
  @Test 
  public void parsingTest3() throws InvalidSemanticPropertySpecificationException, IOException, UnknownPropertyException, InvalidSemanticPropertyUseException, SemanticPropertyNotValidAtScopeException {
    handler.add(new File(PATH + "../concurrency_full.yaml"));
    handler.parse("concurrency SPECIAL 'dsfasdfads'", "concurrency", LevelId.BON_FORMAL);
    handler.parse("concurrency SPECIAL \"dsf'asd'fads\"", "concurrency", LevelId.BON_FORMAL);    
  }
  
  @Test(expected=UnknownVariableIdentifierException.class)
  public void parsingTest4() throws InvalidSemanticPropertySpecificationException, IOException, UnknownPropertyException, InvalidSemanticPropertyUseException, SemanticPropertyNotValidAtScopeException, UnknownVariableIdentifierException {
    handler.add(new File(PATH + "../concurrency_full.yaml"));
    SemanticPropertyInstance inst = handler.parse("concurrency TIMEOUT 5 java.lang.Exception", "concurrency", LevelId.BON_FORMAL);
    inst.getVariable("xxx");
  }
  
  @Test
  public void parsingTest5() throws InvalidSemanticPropertySpecificationException, IOException, UnknownPropertyException, InvalidSemanticPropertyUseException, SemanticPropertyNotValidAtScopeException, UnknownVariableIdentifierException {
    handler.add(new File(PATH + "../concurrency_full.yaml"));
    SemanticPropertyInstance inst = handler.parse("concurrency TIMEOUT 5 java.lang.Exception", "concurrency", LevelId.BON_FORMAL);
    assertEquals(inst.getVariable("CONCURRENT"), "TIMEOUT");
    assertEquals(inst.getVariable("to"), 5);
    assertEquals(inst.getVariable("e"), "java.lang.Exception");
  }
  
  @Test
  public void parsingTest6() throws InvalidSemanticPropertySpecificationException, IOException, UnknownPropertyException, InvalidSemanticPropertyUseException, SemanticPropertyNotValidAtScopeException, UnknownVariableIdentifierException {
    handler.add(new File(PATH + "../concurrency_full.yaml"));
    SemanticPropertyInstance inst = handler.parse("concurrency TIMEOUT 5 java.lang.Exception", "concurrency", LevelId.BON_FORMAL);
    assertEquals(inst.getVariable("to"), 5);
  }
  
  @Test 
  public void refinementTest1() throws InvalidSemanticPropertySpecificationException, IOException, UnknownPropertyException, InvalidSemanticPropertyUseException, SemanticPropertyNotValidAtScopeException, IncompatibleSemanticPropertyInstancesException, InvalidRefinementException {
    handler.add(new File(PATH + "../concurrency_full.yaml"));
    SemanticPropertyInstance inst = handler.parse("concurrency SEQUENTIAL", "concurrency", LevelId.BON_FORMAL);
    SemanticPropertyInstance refInst = handler.generate(inst, LevelId.JAVA_JML);
    assertEquals(refInst.toString(), "concurrency SEQUENTIAL");
  }
  
}
