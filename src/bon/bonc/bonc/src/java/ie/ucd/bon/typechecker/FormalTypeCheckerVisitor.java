package ie.ucd.bon.typechecker;

import ie.ucd.bon.Main;
import ie.ucd.bon.ast.AbstractVisitorWithAdditions;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.ClassInterface;
import ie.ucd.bon.ast.ClassName;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.Constants;
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
import ie.ucd.bon.util.Converter;
import ie.ucd.bon.util.HashMapStack;
import ie.ucd.bon.util.STUtil;
import ie.ucd.bon.util.StringUtil;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
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

    for (FormalGeneric generic : generics) {
      if (generic.type != null) {
        checkValidType(generic.type);
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
      Clazz parentClazz = st.classes.get(parent.identifier);
      if (parentClazz == null) {
        problems.addProblem(new InvalidFormalClassTypeError(parent.getLocation(), parent.getIdentifier()));
      } else {
        checkActualGenerics(parent, parentClazz, context.clazz);
      }
    }

    visitAll(features);
    visitAll(invariant);
  }
  
  private boolean checkValidType(Type type) {
    Clazz c = classForName(type.identifier);
    if (c == null) {
      problems.addProblem(new InvalidFormalClassTypeError(type.location.shortenToLength(type.identifier.length()), type.identifier));
      return false;
    } else {
      if (c.generics.size() != type.actualGenerics.size()) {
        problems.addProblem(new InvalidNumberOfGenericsProvided(type.location, type.identifier, c.generics.size(), type.actualGenerics.size()));
      }
      for (Type actual : type.actualGenerics) {
        if (!checkValidType(actual)) {
          return false;
        }
      }
      return true;
    }
  }

  private Clazz classForName(String name) {
    return st.classes.get(name);
  }
  
  private void checkActualGenerics(Type inheritsType, Clazz inheritedClazz, Clazz clazzInheriting) {
    List<Type> actualGenerics = inheritsType.actualGenerics;
    List<FormalGeneric> formalGenerics = inheritedClazz.generics;
    
    //TODO check every type used in actual is valid (i.e. in st or generic binder for this class)
    
    if (actualGenerics.size() != formalGenerics.size()) {
      problems.addProblem(new InvalidNumberOfGenericsProvided(inheritsType.getLocation(), inheritsType.identifier, formalGenerics.size(), actualGenerics.size()));
      return; //No point in checking further
    }
    
    Map<String,Type> classInheritingBindings = new HashMap<String,Type>();
    for (FormalGeneric classInheritingGeneric : clazzInheriting.generics) {
      classInheritingBindings.put(classInheritingGeneric.identifier, 
                                  classInheritingGeneric.type == null ? 
                                        Type.mk("ANY", Constants.EMPTY_TYPE_LIST, classInheritingGeneric.location)
                                      : classInheritingGeneric.type); 
    }
    
    //Instantiate actual type using classes generic type binders
    List<Type> actualGenericsInst = new ArrayList<Type>();
    for (Type actualGeneric : actualGenerics) {
      Type inst = instantiate(actualGeneric, classInheritingBindings);
      actualGenericsInst.add(inst);
      checkValidType(inst);
    }
    
    Map<String,Type> binderContext = new HashMap<String,Type>();
    for (int i=0; i < actualGenericsInst.size(); i++) {
      Type actualGenericInst = actualGenericsInst.get(i);
      FormalGeneric formalGeneric = formalGenerics.get(i);

      //Deal with using binders in subsequent formal generics
      Type formalGenericType = formalGeneric.type;
      Type formalGenericTypeInst = formalGenericType == null ?
            Type.mk("ANY", Constants.EMPTY_TYPE_LIST, formalGeneric.location)
          : instantiate(formalGenericType, binderContext);  
      Main.logDebug("formalGenericTypeInst = " + StringUtil.prettyPrint(formalGenericTypeInst));
      
      //Check compatible types
      if (!STUtil.isClassAncestorOrEqual(formalGenericTypeInst.identifier, actualGenericInst.identifier, st)) {
        problems.addProblem(new TypeMismatchWithExplanationError(actualGenericInst.location, "Invalid type for generic parameter to " + inheritsType.identifier + ". ", formalGenericTypeInst.toString(), actualGenericInst.toString()));
        return;
      }
      
      //Check generics are identical, but at the level of the formalGeneric
      
      
      //Add the actual generic as a new binder
      binderContext.put(formalGeneric.identifier, actualGenericInst);
    }

  }
  
  private Type deriveParentType(Type actual, Type parent, final BONST st) {
    //Find inheritance path to actual
    List<String> inhPathToParent = st.simpleClassInheritanceGraph.findPath(actual.identifier, parent.identifier, Converter.<String>identityConverter());
    System.out.println("Found inheritance path: " + inhPathToParent + " for " + actual + " to " + parent);
    Collection<Clazz> inhPathToParentAsClazzes = new Converter<String,Clazz>() {
      public Clazz convert(String toConvert) {
        return st.classes.get(toConvert);
      }
    }.convert(inhPathToParent);
    
    Type current = actual;
    
    Iterator<Clazz> inhPathIterator = inhPathToParentAsClazzes.iterator();
    inhPathIterator.next();
    while (inhPathIterator.hasNext()) {
//      current = raiseTo(current, inhPathIterator.next());
    }
    
    return current;
  }
  
//  private Type raiseTo(Type current, Clazz directParent) {
//    
//  }
  
  private Type instantiate(Type type, Map<String,Type> binders) {
    Main.logDebug("Type: " + StringUtil.prettyPrint(type));
    Main.logDebug("Binders: " + binders.toString());
    String instantiatedTypeName = binders.containsKey(type.identifier) ? binders.get(type.identifier).identifier : type.identifier;
    List<Type> instantiatedGenerics = new ArrayList<Type>(type.actualGenerics.size());
    for (Type unin : type.actualGenerics) {
      instantiatedGenerics.add(instantiate(unin, binders));
    }
    return Type.mk(instantiatedTypeName, instantiatedGenerics, type.location);
  }
  
  private boolean identicalType(Type type1, Type type2) {
    if (!type1.identifier.equals(type2.identifier)) {
      return false;
    }
    List<Type> type1ActualGenerics = type1.actualGenerics;
    List<Type> type2ActualGenerics = type2.actualGenerics;
    if (type1ActualGenerics.size() != type2ActualGenerics.size()) {
      return false;
    }
    for (int i=0; i < type1ActualGenerics.size(); i++) {
      Type type1ActualGeneric = type1ActualGenerics.get(i);
      Type type2ActualGeneric = type2ActualGenerics.get(i);
      if (!identicalType(type1ActualGeneric, type2ActualGeneric)) {
        return false;
      }
    }
    return true;
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
  
  
  public Problems getProblems() {
    return problems;
  }
  
}
