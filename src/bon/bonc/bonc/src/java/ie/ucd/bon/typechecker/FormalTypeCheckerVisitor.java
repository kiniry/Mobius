package ie.ucd.bon.typechecker;

import ie.ucd.bon.Main;
import ie.ucd.bon.ast.AbstractVisitorWithAdditions;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.IVisitorWithAdditions;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.SpecificationElement;
import ie.ucd.bon.ast.StaticComponent;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.Clazz.Mod;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.typechecker.errors.InvalidFormalClassTypeError;
import ie.ucd.bon.typechecker.errors.InvalidNumberOfGenericsProvided;
import ie.ucd.bon.typechecker.errors.TypeMismatchWithExplanationError;
import ie.ucd.bon.util.HashMapStack;
import ie.ucd.bon.util.STUtil;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class FormalTypeCheckerVisitor extends AbstractVisitorWithAdditions implements IVisitorWithAdditions {

  private final BONST st;
  private final VisitorContext context;
  private final Problems problems;
  private final HashMapStack<String,Type> tc;

  public FormalTypeCheckerVisitor(BONST st) {
    this.st = st;
    this.problems = new Problems("FORMALTC");
    this.context = new VisitorContext();
    this.tc = new HashMapStack<String,Type>();
    
    initialiseTC();
  }
  
  private void initialiseTC() {
    tc.putAll(st.classNameToTypeMap); 
  }
  
  @Override
  public void visitClazz(Clazz node, ClassName name, List<FormalGeneric> generics,
      Mod mod, ClassInterface classInterface, Boolean reused,
      Boolean persistent, Boolean interfaced, String comment, SourceLocation loc) {
    context.clazz = node;

    if (st.filledInGenericsMap.containsKey(node)) {
      for (Type t : st.filledInGenericsMap.get(node)) {
        checkValidType(t);
      }
    }
    
    visitNode(classInterface);
    context.clazz = null;
  }
  
  @Override
  public void visitClassInterface(ClassInterface node, List<Feature> features,
      List<Type> parents, List<Expression> invariant, Indexing indexing,
      SourceLocation loc) {

    for (Type parent : parents) {
      Type filledInParent = STUtil.fillInPlaceHolders(parent, st.filledInGenericNamesMap.getSecondDimension(context.clazz), false);
      checkValidType(filledInParent);
    }

    visitAll(features);
    visitAll(invariant);
  }
  
  @Override
  public void visitBonSourceFile(BonSourceFile node, List<SpecificationElement> bonSpecification, Indexing indexing, SourceLocation loc) {
    visitAll(bonSpecification);
  }
  
  @Override
  public void visitStaticDiagram(StaticDiagram node, List<StaticComponent> components, String extendedId, String comment, SourceLocation loc) {
    visitAll(components);
  }
  
  @Override
  public void visitCluster(Cluster node, String name, List<StaticComponent> components, Boolean reused, String comment, SourceLocation loc) {
    visitAll(components);
  }
  
  
  private boolean checkValidType(Type type) {
    Main.logDebug("Checking " + type + " is a valid type");
    Clazz c = classForName(type.identifier);
    if (c == null) {
      problems.addProblem(new InvalidFormalClassTypeError(type.location.shortenToLength(type.identifier.length()), type.identifier));
      return false;
    } else {
      if (c.generics.size() != type.actualGenerics.size()) {
        problems.addProblem(new InvalidNumberOfGenericsProvided(type.location, type.identifier, c.generics.size(), type.actualGenerics.size()));
      }
      
      List<Type> filledInGenerics = st.filledInGenericsMap.get(c);
      if (filledInGenerics != null) {
        for (int i=0; i < filledInGenerics.size(); i++) {
          Type actual = type.actualGenerics.get(i);
          Type formal = filledInGenerics.get(i);
          
          if (!checkValidType(actual)) {
            return false;
          }
          InstantiatedClassType ict = instantiateClass(classForName(actual.identifier), actual);
          if (!checkValidSubtypeOrEqual(ict, formal, "Invalid type for generic parameter. ")) {
            return false;
          }
          
        }
      }
      return true;
    }
  }

  private Clazz classForName(String name) {
    return st.classes.get(name);
  }
  
  private InstantiatedClassType instantiateClass(Clazz c, Type actualType) {
    Map<String,Type> binders = new HashMap<String,Type>();
    List<Type> actualGenerics = actualType.actualGenerics;
    
    //Check same num of generics
    if (actualGenerics.size() != c.generics.size()) {
      problems.addProblem(new InvalidNumberOfGenericsProvided(actualType.getLocation(), actualType.identifier, c.generics.size(), actualGenerics.size()));
      return null;
    }
    
    for (int i=0; i < c.generics.size(); i++) {
      FormalGeneric formalGeneric = c.generics.get(i);
      Type suppliedGeneric = actualGenerics.get(i);
      
      //Get actual constraint by filling in binders in type constraint (or ANY if no constraint)
      Type formalGenericConstraint = formalGeneric.type == null ? 
          STUtil.anyType(formalGeneric.location) 
          : STUtil.fillInPlaceHolders(formalGeneric.type, binders, true);
          
      Clazz suppliedGenericClazz = classForName(suppliedGeneric.identifier);
      if (suppliedGenericClazz == null) {
        return null;
      }
      //Check suppliedGeneric is ok for filledInFormalGenericConstraint
      InstantiatedClassType ict = instantiateClass(suppliedGenericClazz, suppliedGeneric);
      if (!checkValidSubtypeOrEqual(ict, formalGenericConstraint, "SPOOF")) {
        return null;
      }      
          
      binders.put(formalGeneric.identifier, suppliedGeneric);
    }

    return new InstantiatedClassType(c, binders, actualType);
  }
  
  private boolean checkValidSubtypeOrEqual(InstantiatedClassType instType1, Type type2, String notAncestorMessage) {
    Type type1 = instType1.type;
    
    if (type1.identifier.equals(type2.identifier)) {
      boolean valid = true;
      for (int i=0; i < type1.actualGenerics.size(); i++) {
        if (!typeEquality(type1.actualGenerics.get(i),type2.actualGenerics.get(i))) {
          //TODO problem
          valid = false;
        }
      }
      if (!valid) {
        return false;
      }
    }    
    
    //We're not the exact type, check if subtype
    if (!STUtil.isClassAncestorOrEqual(type2.identifier, type1.identifier, st)) {
      problems.addProblem(new TypeMismatchWithExplanationError(type1.location, notAncestorMessage, type2.toString(), type1.toString()));
      return false;
    }

    //We're a subtype, so we must raise ourself one level towards the ancestor, then ask again
    Clazz type1Clazz = classForName(type1.identifier);
    if (type1Clazz == null) {
      return false;
    }

    //Find the first parent that has the same ancestor, move to that level
    boolean found = false;
    if (type1Clazz.classInterface != null) {
      for (Type parent : type1Clazz.classInterface.parents) {
        if (STUtil.isClassAncestorOrEqual(type2.identifier, parent.identifier, st)) {
          Type parentFilledIn = STUtil.fillInPlaceHolders(parent, instType1.bindersMap, false);
          InstantiatedClassType ict = instantiateClass(classForName(parent.identifier), parentFilledIn);
          if (!checkValidSubtypeOrEqual(ict, type2, notAncestorMessage)) {
            return false;
          }
          found = true;
          break;
        }
      }
    }
    if (!found) {
      //TODO - shouldn't happen?
      return false;
    }
    return true;
  }
  
  private boolean typeEquality(Type type1, Type type2) {
    if (!type1.identifier.equals(type2.identifier)) {
      return false;
    }
    if (type1.actualGenerics.size() != type2.actualGenerics.size()) {
      return false;
    }
    for (int i=0; i < type1.actualGenerics.size(); i++) {
      if (!typeEquality(type1.actualGenerics.get(i),type2.actualGenerics.get(i))) {
        return false;
      }
    }
    return true;
  }
  
  public Problems getProblems() {
    return problems;
  }
  
}
