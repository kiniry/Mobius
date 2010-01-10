/**
 * Package for input.
 */
package input;

import static com.sun.tools.javac.code.Flags.ENUM;
import static com.sun.tools.javac.code.Flags.INTERFACE;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;

import javax.lang.model.element.Modifier;

import log.CCLevel;
import log.CCLogRecord;
import logic.BeetlzExpression;
import logic.Operator;
import logic.BeetlzExpression.ArithmeticExpression;
import logic.BeetlzExpression.ArrayaccessExpression;
import logic.BeetlzExpression.EqualityExpression;
import logic.BeetlzExpression.EquivalenceExpression;
import logic.BeetlzExpression.IdentifierExpression;
import logic.BeetlzExpression.ImpliesExpression;
import logic.BeetlzExpression.InformalExpression;
import logic.BeetlzExpression.Keyword;
import logic.BeetlzExpression.LiteralExpression;
import logic.BeetlzExpression.LogicalExpression;
import logic.BeetlzExpression.MemberaccessExpression;
import logic.BeetlzExpression.MethodcallExpression;
import logic.BeetlzExpression.Nullity;
import logic.BeetlzExpression.RelationalExpression;
import logic.BeetlzExpression.UnaryExpression;
import logic.BeetlzExpression.Keyword.Keywords;
import main.Beetlz;

import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlToken;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlSpecs.FieldSpecs;
import org.jmlspecs.openjml.JmlSpecs.MethodSpecs;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;

import structure.ClassStructure;
import structure.FeatureStructure;
import structure.Invariant;
import structure.Signature;
import structure.Spec;
import structure.Visibility;
import utils.BConst;
import utils.FeatureType;
import utils.BeetlzSourceLocation;
import utils.ModifierManager.ClassModifier;
import utils.ModifierManager.ClassType;
import utils.ModifierManager.FeatureModifier;
import utils.ModifierManager.VisibilityModifier;
import utils.smart.FeatureSmartString;
import utils.smart.GenericParameter;
import utils.smart.ParametrizedSmartString;
import utils.smart.SmartString;
import utils.smart.TypeSmartString;
import utils.smart.WildcardSmartString;
import utils.smart.WildcardSmartString.WildcardType;

import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Attribute.Compound;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;
import com.sun.tools.javac.code.Type.ArrayType;
import com.sun.tools.javac.code.Type.ErrorType;
import com.sun.tools.javac.tree.JCTree;

/**
 * Parser for JML and Java information from OpenJML ASTs.
 * Takes JCTree elements and all specification elements and puts the
 * required information into our own data structures.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public final class JmlParser {
  /**  */
  private JmlParser() { }

  /**
   * Parses a class, ie takes the information from JML constructs
   * and puts them into our own data structures.
   * It is not being checked that the specs and symbols actually
   * belong to the same class.
   * @param a_cls class to parse
   * @param the_specs class' specs
   * @param a_sym class' symbol
   * @param a_flat_name simple name of the class
   * @param the_encl_class enclosing class, if present, otherwise null
   * @param a_cu compilation unit, needed for source locations
   * @return parsed class
   */
  public static ClassStructure parseClass(final JCTree.JCClassDecl a_cls,
                                          final TypeSpecs the_specs,
                                          final ClassSymbol a_sym,
                                          final String a_flat_name,
                                          final ClassStructure the_encl_class,
                                          final JmlTree.JmlCompilationUnit a_cu) {

    final SortedSet < ClassModifier > mod       = new TreeSet < ClassModifier > ();
    Visibility vis = new Visibility(VisibilityModifier.PACKAGE_PRIVATE);
    final List < SmartString > generics    = new Vector < SmartString > ();
    final SortedSet < SmartString > interfaces  = new TreeSet < SmartString > ();
    final List < SmartString > pack = new Vector < SmartString > ();
    //Class name
    final TypeSmartString name = new TypeSmartString(a_flat_name);

    //Package
    if (a_sym.packge() != null) {
      final String[] parts = a_sym.packge().toString().split("\\."); //$NON-NLS-1$
      for (final String s : parts) {
        pack.add(new SmartString(s));
      }
    }
    //Enum?
    if ((a_cls.mods.flags & ENUM) != 0) { //we have enum
      mod.add(ClassModifier.ENUM);
    }
    //Interface?
    if ((a_cls.mods.flags & INTERFACE) != 0) {
      mod.add(ClassModifier.ABSTRACT);
      mod.add(ClassModifier.JAVA_INTERFACE);
    }

    //Modifier
    for (final Modifier m : a_cls.getModifiers().getFlags()) {
      if (m == Modifier.ABSTRACT) {
        mod.add(ClassModifier.ABSTRACT);
      } else if (m == Modifier.FINAL) {
        mod.add(ClassModifier.FINAL);
      } else if (m == Modifier.PRIVATE) {
        vis = new Visibility(VisibilityModifier.PRIVATE);
      } else if (m == Modifier.PROTECTED) {
        vis = new Visibility(VisibilityModifier.PROTECTED);
      } else if (m == Modifier.PUBLIC) {
        vis = new Visibility(VisibilityModifier.PUBLIC);
      } else if (m == Modifier.STATIC) {
        mod.add(ClassModifier.STATIC);
      } else if (m == Modifier.STRICTFP) {
        mod.add(ClassModifier.STRICTFP);
      }
    }
    //Generics
    if (a_cls.getTypeParameters().size() > 0) {
      mod.add(ClassModifier.GENERIC);

      final List < JCTree.JCTypeParameter > g = a_cls.getTypeParameters();
      for (final JCTree.JCTypeParameter f : g) {
        if (f.getBounds().size() > 0) {
          final List < SmartString > list = new Vector < SmartString > ();
          for (final JCTree.JCExpression e : f.getBounds()) {
            list.add(getType(e));
          }
          generics.add(new GenericParameter(f.toString(), f.getName().toString(), list));
        } else {
          generics.add(new GenericParameter(f.toString(),
                                            f.getName().toString(),
                                            new Vector < SmartString > ()));
        }
      }
    }

    //Inheritance
    if (a_cls.getExtendsClause() != null) {
      if (a_cls.getExtendsClause().getKind() == Tree.Kind.IDENTIFIER ||
          a_cls.getExtendsClause().getKind() == Tree.Kind.PARAMETERIZED_TYPE) {
        interfaces.add(getType((JCTree.JCExpression)a_cls.getExtendsClause()));
      }
    }

    //Interfaces
    if (a_cls.getImplementsClause().length() > 0) {
      for (final JCTree.JCExpression i : a_cls.getImplementsClause()) {
        interfaces.add(getType(i));
      }
    }

    //SourceLocation
    //TODO use exact position of identifier, but how to do this?
    final File fileName = new File(a_cu.sourcefile.toUri().getPath());
    //final int startPos = a_cls.getStartPosition();
    int startPos = a_cls.pos().getStartPosition() + a_cls.mods.toString().length();
    if (!a_cls.mods.toString().contains("interface")) {
      startPos += 6;
    }
    //final int endPos = a_cls.getEndPosition(a_cu.endPositions);
    final int endPos = startPos + a_cls.name.toString().length();
    final int lineNum = a_cu.getLineMap().getLineNumber(startPos);
    final int posInLine = a_cu.getLineMap().getColumnNumber(startPos);
    
    final BeetlzSourceLocation src = new BeetlzSourceLocation(fileName, lineNum, posInLine, startPos, endPos, lineNum, true);
    //Create class
    final ClassStructure parsedClass = new ClassStructure(ClassType.JAVA, mod,
                                                          vis, generics, name,
                                                          interfaces,
                                                          pack, src);
    if (the_encl_class != null) {
      the_encl_class.addAggregation(name);
    }
    final Map < JCTree, String > docs = a_cu.docComments;

    if (docs != null) {
      for (final JCTree t : docs.keySet()) {
        if (t instanceof JCTree.JCClassDecl) {
          if (((JCTree.JCClassDecl)t).name.equals(a_cls.name)) {
            setComment(parsedClass, docs.get(t));
          }
        }
      }
    }

    if (the_specs != null) {
      parsedClass.setInvariant(JmlParser.parseClassSpecs(the_specs));
    }

    //Annotations?
    for (final Compound an : a_sym.getAnnotationMirrors()) {
      if (an.getAnnotationType().toString().
          equals("org.jmlspecs.annotation.NullableByDefault")) { //$NON-NLS-1$
        parsedClass.setNullity(Nullity.NULLABLE);
      }
      if (an.getAnnotationType().toString().
          equals("org.jmlspecs.annotation.Pure")) { //$NON-NLS-1$
        parsedClass.setPure(true);
      }
    }

    return parsedClass;
  }

  /**
   * Parse a method and put the information into our
   * data structures.
   * @param a_method feature to parse
   * @param the_specs feature specs
   * @param an_encl_class class where this feature is
   * @param the_cu compilation unit, needed for source locations
   * @return specs
   */
  public static FeatureStructure parseMethod(final JmlTree.JmlMethodDecl a_method,
                                             final JmlSpecs.MethodSpecs the_specs,
                                             final ClassStructure an_encl_class,
                                             final JmlTree.JmlCompilationUnit the_cu) {

    final SortedSet < FeatureModifier > mod = new TreeSet < FeatureModifier > ();
    Visibility vis = new Visibility(VisibilityModifier.PACKAGE_PRIVATE);
    if(an_encl_class.isInterface())
      vis = new Visibility(VisibilityModifier.PUBLIC);
    
    SmartString return_value = SmartString.getVoid();
    final Map < String , SmartString > params = new HashMap < String, SmartString > ();
    //Method name
    final FeatureSmartString name = new FeatureSmartString(a_method.getName().toString());
    //Generics
    final List < SmartString > generics    = new Vector < SmartString > ();
    if (a_method.getTypeParameters().size() > 0) {
      final List < JCTree.JCTypeParameter > g = a_method.getTypeParameters();
      for (final JCTree.JCTypeParameter ff : g) {
        if (ff.getBounds().size() > 0) {
          final List < SmartString > list = new Vector < SmartString > ();
          for (final JCTree.JCExpression e : ff.getBounds()) {
            list.add(getType(e));
          }
          generics.add(new GenericParameter(ff.toString(), ff.getName().toString(), list));
        } else {
          generics.add(new GenericParameter(ff.toString(), ff.getName().toString(),
                                            new Vector < SmartString > ()));
        }
      }
    }
    //Annotations (need annotations first to distinguish model class)
    boolean pure = false;
    boolean encl_pure = false;
    for (final JCTree.JCAnnotation an : a_method.getModifiers().getAnnotations()) {
      if (an.getAnnotationType().toString().equals("Override")) { //$NON-NLS-1$
        mod.add(FeatureModifier.REDEFINED);
      } else if (an.getAnnotationType().toString().
          equals("org.jmlspecs.annotation.Pure")) { //$NON-NLS-1$
        mod.add(FeatureModifier.PURE);
        pure = true;
      } else if (an.getAnnotationType().toString().
          equals("org.jmlspecs.annotation.NonNull")) { //$NON-NLS-1$
        return_value.setNullity(Nullity.NON_NULL);
      } else if (an.getAnnotationType().toString().
          equals("org.jmlspecs.annotation.Nullable")) { //$NON-NLS-1$
        return_value.setNullity(Nullity.NULLABLE);
      } else if (an.getAnnotationType().toString().
          equals("org.jmlspecs.annotation.Model")) { //$NON-NLS-1$
        mod.add(FeatureModifier.MODEL);
      }
    }
    if (an_encl_class.isPure()) {
      encl_pure = true;
    }

    //Modifier
    for (final Modifier m : a_method.getModifiers().getFlags()) {
      if (m == Modifier.ABSTRACT) {
        mod.add(FeatureModifier.ABSTRACT);
      } else if (m == Modifier.FINAL) {
        mod.add(FeatureModifier.FINAL);
      } else if (m == Modifier.PRIVATE) {
        vis = new Visibility(VisibilityModifier.PRIVATE);
      } else if (m == Modifier.PROTECTED) {
        vis = new Visibility(VisibilityModifier.PROTECTED);
      } else if (m == Modifier.PUBLIC) {
        vis = new Visibility(VisibilityModifier.PUBLIC);
      } else if (m == Modifier.STATIC) {
        mod.add(FeatureModifier.STATIC);
      } else if (m == Modifier.STRICTFP) {
        mod.add(FeatureModifier.STRICTFP);
      } else if (m == Modifier.NATIVE) {
        mod.add(FeatureModifier.NATIVE);
      } else if (m == Modifier.SYNCHRONIZED) {
        mod.add(FeatureModifier.SYNCHRONIZED);
      } else if (m == Modifier.TRANSIENT) {
        mod.add(FeatureModifier.TRANSIENT);
      } else if (m == Modifier.VOLATILE) {
        mod.add(FeatureModifier.VOLATILE);
      }
    }
    

    //Return type
    if (a_method.getReturnType() != null) {
      final JCTree type = a_method.getReturnType();
      if (type instanceof JCTree.JCExpression) {
        return_value = getType((JCTree.JCExpression)type);
      } else {
        return_value = new SmartString(type.toString());
      }
    }

    //Arguments
    for (final JCTree.JCVariableDecl v : a_method.getParameters()) {
      final JCTree type = v.vartype;
      SmartString par;
      if (type instanceof JCTree.JCExpression) {
        par = getType((JCTree.JCExpression)type);
      } else {
        par = new SmartString(type.toString());
      }
      for (final Compound an : v.sym.getAnnotationMirrors()) {
        if (an.getAnnotationType().toString().
            equals("org.jmlspecs.annotation.NonNull")) { //$NON-NLS-1$
          par.setNullity(Nullity.NON_NULL);
        }
        if (an.getAnnotationType().toString().
            equals("org.jmlspecs.annotation.Nullable")) { //$NON-NLS-1$
          par.setNullity(Nullity.NULLABLE);
        }
      }
      params.put(v.name.toString(), par);
    }
    if (an_encl_class.getNullity() == Nullity.NULLABLE) {
      if (return_value.getNullity() == null) {
        return_value.setNullity(Nullity.NULLABLE);
      }
      for (final SmartString s : params.values()) {
        if (s.getNullity() == null) {
          s.setNullity(Nullity.NULLABLE);
        }
      }
    }
    final Signature sign = Signature.getJavaSignature(return_value, params);
    //Specs
    final List < Spec > spec =
      JmlParser.parseFeatureSpecs(a_method.methodSpecsCombined, pure, return_value, encl_pure);
    if (encl_pure && spec.get(0).getFeatureType() == FeatureType.QUERY) {
      mod.add(FeatureModifier.PURE);
    }

    //SourceLocation
    final File fileName = new File(the_cu.sourcefile.toUri().getPath());
    final int lineNum = the_cu.getLineMap().getLineNumber(a_method.getStartPosition());
    final int startPos = a_method.getStartPosition() + a_method.getModifiers().toString().length();
    final int endPos = startPos + a_method.name.toString().length();
    final int posInLine = the_cu.getLineMap().getColumnNumber(startPos);
    
    final BeetlzSourceLocation src = new BeetlzSourceLocation(fileName, lineNum, posInLine, startPos, endPos, lineNum, true);

    final FeatureStructure feat = new FeatureStructure(mod, vis, name, sign, spec,
                                                       src, null, null, an_encl_class);
    feat.setGenerics(generics);

    return feat;
  }

  /**
   * Parse a variable.
   * @param a_variable variable symbol
   * @param the_specs variable's specs
   * @param an_encl_class class where this variable is
   * @param the_cu compilation unit for source locations
   * @return specs
   */
  public static FeatureStructure parseVariable(final VarSymbol a_variable,
                                               final FieldSpecs the_specs,
                                               final ClassStructure an_encl_class,
                                               final JmlTree.JmlCompilationUnit the_cu) {

    final SortedSet < FeatureModifier > mod = new TreeSet < FeatureModifier > ();
    Visibility vis                          =
      new Visibility(VisibilityModifier.PACKAGE_PRIVATE);
    final Map < String , SmartString > args = new HashMap < String, SmartString > ();
    final FeatureSmartString name =
      new FeatureSmartString(a_variable.getQualifiedName().toString());
    //Modifier
    for (final Modifier m : a_variable.getModifiers()) {
      if (m == Modifier.ABSTRACT) {
        mod.add(FeatureModifier.ABSTRACT);
      } else if (m == Modifier.FINAL) {
        mod.add(FeatureModifier.FINAL);
      } else if (m == Modifier.PRIVATE) {
        vis = new Visibility(VisibilityModifier.PRIVATE);
      } else if (m == Modifier.PROTECTED) {
        vis = new Visibility(VisibilityModifier.PROTECTED);
      } else if (m == Modifier.PUBLIC) {
        vis = new Visibility(VisibilityModifier.PUBLIC);
      } else if (m == Modifier.STATIC) {
        mod.add(FeatureModifier.STATIC);
      } else if (m == Modifier.STRICTFP) {
        mod.add(FeatureModifier.STRICTFP);
      } else if (m == Modifier.NATIVE) {
        mod.add(FeatureModifier.NATIVE);
      } else if (m == Modifier.SYNCHRONIZED) {
        mod.add(FeatureModifier.SYNCHRONIZED);
      } else if (m == Modifier.TRANSIENT) {
        mod.add(FeatureModifier.TRANSIENT);
      } else if (m == Modifier.VOLATILE) {
        mod.add(FeatureModifier.VOLATILE);
      }
    }
    //Is the spec visibility different?
    final VisibilityModifier specVis = parseSpecVisibility(a_variable);

    if (specVis != null) {
      vis.setSpecVisibility(specVis);
    }
    //Specs:
    final List < Spec > spec = new Vector < Spec > ();
    spec.add(JmlParser.parseVariableSpecs(a_variable, the_specs));

    //Annotations
    for (final Compound an : a_variable.getAnnotationMirrors()) {
      if (an.toString().equals("@org.jmlspecs.annotation.Ghost")) { //$NON-NLS-1$
        mod.add(FeatureModifier.GHOST);
      }
      if (an.toString().equals("@org.jmlspecs.annotation.Model")) { //$NON-NLS-1$
        mod.add(FeatureModifier.MODEL);
      }
    }

    //Return value
    SmartString return_value = new SmartString();
    if (a_variable.type != null) {
      return_value = getType(a_variable.type);
      for (final Compound an : a_variable.getAnnotationMirrors()) {
        if (an.getAnnotationType().toString().
            equals("org.jmlspecs.annotation.NonNull")) { //$NON-NLS-1$
          return_value.setNullity(Nullity.NON_NULL);
        }
        if (an.getAnnotationType().toString().
            equals("org.jmlspecs.annotation.Nullable")) { //$NON-NLS-1$
          return_value.setNullity(Nullity.NULLABLE);
        }
      }
    }
    if (an_encl_class.getNullity() == Nullity.NULLABLE) {
      if (return_value.getNullity() == null) {
        return_value.setNullity(Nullity.NULLABLE);
      }
    }
    final Signature sign = Signature.getJavaSignature(return_value, args);

    //SourceLocation
    final File fileName = new File(the_cu.sourcefile.toUri().getPath());
    final int lineNum = the_cu.getLineMap().getLineNumber(a_variable.pos);
    final BeetlzSourceLocation src = new BeetlzSourceLocation(fileName, lineNum, true);

    return new FeatureStructure(mod, vis, name, sign, spec,
                                src, null, null, an_encl_class);
  }

  /**
   * Get a smart string from a JCExpression, and parse it accordingly
   * to the correct subclass.
   * @param an_expr expression to parse
   * @return parsed expression
   */
  private static SmartString getType(final JCTree.JCExpression an_expr) {
    if (an_expr.getKind() == Kind.PRIMITIVE_TYPE) {
      return new SmartString(an_expr.toString());
    }
    if (an_expr.getKind() == Kind.IDENTIFIER) {
      return new TypeSmartString(an_expr.toString());
    }
    if (an_expr.getKind() == Kind.PARAMETERIZED_TYPE) {
      final JCTree.JCTypeApply type = (JCTree.JCTypeApply) an_expr;
      final SmartString name = new TypeSmartString(type.clazz.toString());
      final List < SmartString > params = new Vector < SmartString > ();
      for (final JCTree.JCExpression ee : type.getTypeArguments()) {
        params.add(getType(ee));
      }
      return new ParametrizedSmartString(type.toString(), name, params);
    }
    if (an_expr.getKind() == Kind.MEMBER_SELECT) {
      final int index = an_expr.toString().lastIndexOf('.');
      String temp = ""; //$NON-NLS-1$
      if (index != -1 && index != an_expr.toString().length()) {
        temp = an_expr.toString().substring(index + 1);
      }
      return new TypeSmartString(temp);
    }
    if (an_expr.getKind() == Kind.ARRAY_TYPE) {
      final JCTree.JCArrayTypeTree arr = (JCTree.JCArrayTypeTree) an_expr;
      final String fullname = "Aray<" +
        arr.getType().toString() + ">"; //$NON-NLS-1$ //$NON-NLS-2$
      final List < SmartString > list = new Vector < SmartString > ();
      list.add(getType(arr.elemtype));
      return new ParametrizedSmartString(fullname,
                                         new TypeSmartString("Aray"), //$NON-NLS-1$
                                         list);
    }
    if (an_expr.getKind() == Kind.SUPER_WILDCARD) {
      final JCTree.JCWildcard w = (JCTree.JCWildcard) an_expr;
      return new WildcardSmartString(w.toString(), WildcardType.SUPER,
                                     getType((JCTree.JCExpression)w.getBound()));
    }
    if (an_expr.getKind() == Kind.EXTENDS_WILDCARD) {
      final JCTree.JCWildcard w = (JCTree.JCWildcard) an_expr;
      return new WildcardSmartString(w.toString(), WildcardType.EXTENDS,
                                     getType((JCTree.JCExpression)w.getBound()));
    }
    if (an_expr.getKind() == Kind.UNBOUNDED_WILDCARD) {
      return WildcardSmartString.getJavaWildcard();
    }
    return new SmartString(an_expr.toString());

  }

  /**
   * Get a smart string from a JCExpression, and parse it accordingly
   * to the correct subclass.
   * @param a_type type to parse
   * @return parsed type
   */
  private static SmartString getType(final Type a_type) {
    final int two = 2;
    if (a_type instanceof Type.ClassType && !a_type.isParameterized()) { //normal class type
      return new TypeSmartString(a_type.toString());
    }
    if (a_type instanceof Type.ClassType && a_type.isParameterized()) { //params class type
      final Type.ClassType c = (Type.ClassType) a_type;
      final String fullname = c.toString();
      final SmartString name = new TypeSmartString(a_type.asElement().toString());
      final List < SmartString > params = new Vector < SmartString > ();
      for (final Type ee : a_type.allparams()) {
        params.add(getType(ee));
      }
      return new ParametrizedSmartString(fullname, name, params);
    }
    //array
    if (a_type instanceof ArrayType) {
      final String simpleType =
        a_type.toString().substring(0, a_type.toString().length() - two);
      final List < SmartString > list = new Vector < SmartString > ();
      list.add(new TypeSmartString(simpleType));
      return
        new ParametrizedSmartString("Aray<" + simpleType + ">", //$NON-NLS-1$ //$NON-NLS-2$
                                         new TypeSmartString("Aray"), //$NON-NLS-1$
                                         list);
    }
    //error
    if (a_type instanceof ErrorType) {
      Beetlz.getWaitingRecords().
        add(new CCLogRecord(CCLevel.COMPILATION_ERROR, null,
                          Beetlz.getResourceBundle().
                          getString("JmlParser.javaComplError") + //$NON-NLS-1$
                          a_type));
    }
    return new SmartString(a_type.toString());
  }

  /**
   * Parse a class' specification.
   * Only parses clauses that are recognised and potentially
   * compared to BON.
   * @param the_specs class specs
   * @return parsed class specs
   */
  private static Invariant parseClassSpecs(final TypeSpecs the_specs) {
    final List < BeetlzExpression > clauses = new Vector < BeetlzExpression > ();
    final List < BeetlzExpression > history = new Vector < BeetlzExpression > ();

    for (final JmlTree.JmlTypeClause c : the_specs.clauses) {
      if (c instanceof JmlTree.JmlTypeClauseExpr) {
        final JmlTree.JmlTypeClauseExpr expr = (JmlTree.JmlTypeClauseExpr) c;
        final BeetlzExpression e = parseExpr(expr.expression);
        clauses.addAll(splitBooleanExpressions(e));
      //end JmlTypeClauseExpr
      } else if (c instanceof JmlTree.JmlTypeClauseConstraint) {
        final JmlTree.JmlTypeClauseConstraint expr = (JmlTree.JmlTypeClauseConstraint) c;
        final BeetlzExpression e = parseExpr(expr.expression);
        history.addAll(splitBooleanExpressions(e));
      } else {
        clauses.add(new InformalExpression(c.toString()));
      }
    }
    return new Invariant(clauses, history);
  }

  /**
   * Parse a JML expression to our own representation.
   * @param an_expr expression
   * @return parsed expression
   */
  private static BeetlzExpression parseExpr(final JCTree.JCExpression an_expr) {
    BeetlzExpression new_expr = InformalExpression.EMPTY_COMMENT;
    if (an_expr instanceof JCTree.JCBinary) {
      final JCTree.JCBinary bin = (JCTree.JCBinary) an_expr;
      if (bin.getKind() == Kind.GREATER_THAN) {
        new_expr = new RelationalExpression(parseExpr(bin.lhs),
                                           Operator.GREATER, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.GREATER_THAN_EQUAL) {
        new_expr = new RelationalExpression(parseExpr(bin.lhs),
                                           Operator.GREATER_EQUAL, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.LESS_THAN) {
        new_expr = new RelationalExpression(parseExpr(bin.lhs),
                                           Operator.SMALLER, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.LESS_THAN_EQUAL) {
        new_expr = new RelationalExpression(parseExpr(bin.lhs),
                                           Operator.SMALLER_EQUAL, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.EQUAL_TO) {
        new_expr = new EqualityExpression(parseExpr(bin.lhs),
                                         Operator.EQUAL, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.NOT_EQUAL_TO) {
        new_expr = new EqualityExpression(parseExpr(bin.lhs),
                                         Operator.NOT_EQUAL, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.MULTIPLY) {
        new_expr = new ArithmeticExpression(parseExpr(bin.lhs),
                                           Operator.MULTIPLE, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.DIVIDE) {
        new_expr = new ArithmeticExpression(parseExpr(bin.lhs),
                                           Operator.DIVIDE, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.MINUS) {
        new_expr = new ArithmeticExpression(parseExpr(bin.lhs),
                                           Operator.MINUS, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.PLUS) {
        new_expr = new ArithmeticExpression(parseExpr(bin.lhs),
                                           Operator.PLUS, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.REMAINDER) { //guess this is modulo
        new_expr = new ArithmeticExpression(parseExpr(bin.lhs),
                                           Operator.MODULO, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.CONDITIONAL_AND) {
        new_expr = new LogicalExpression(parseExpr(bin.lhs),
                                        Operator.AND, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.CONDITIONAL_OR) {
        new_expr = new LogicalExpression(parseExpr(bin.lhs),
                                        Operator.OR, parseExpr(bin.rhs));
      } else if (bin.getKind() == Kind.XOR) {
        new_expr = new LogicalExpression(parseExpr(bin.lhs),
                                        Operator.XOR, parseExpr(bin.rhs));
      } else {
        new_expr = new InformalExpression(an_expr.toString());
      }
      //end binary
    } else if (an_expr instanceof JmlTree.JmlBinary) {
      final JmlTree.JmlBinary b = (JmlTree.JmlBinary) an_expr;
      
      if (b.op == JmlToken.IMPLIES) {
        new_expr = new ImpliesExpression(parseExpr(b.lhs), parseExpr(b.rhs));
      } else if (b.op == JmlToken.REVERSE_IMPLIES) {
        new_expr = new ImpliesExpression(parseExpr(b.rhs), parseExpr(b.lhs));
      } else if (b.op == JmlToken.EQUIVALENCE) {
        new_expr = new EquivalenceExpression(parseExpr(b.rhs), Operator.IFF,
                                            parseExpr(b.lhs));
      } else if (b.op == JmlToken.INEQUIVALENCE) {
        new_expr = new EquivalenceExpression(parseExpr(b.rhs), Operator.NOT_IFF,
                                            parseExpr(b.lhs));
      } else {
        new_expr = new InformalExpression(an_expr.toString());
      }
      //end JmlBinary
    } else if (an_expr instanceof JmlTree.JmlSingleton) {
      final JmlTree.JmlSingleton s = (JmlTree.JmlSingleton) an_expr;
      if (s.token == JmlToken.BSRESULT) {
        new_expr = new Keyword(Keywords.RESULT);
      } else if (s.token == JmlToken.INFORMAL_COMMENT) {
        new_expr = InformalExpression.EMPTY_COMMENT;
      } else {
        new_expr = new InformalExpression(an_expr.toString());
      }
      //end JmlSingleton
    } else if (an_expr instanceof JCTree.JCUnary) {
      final JCTree.JCUnary un = (JCTree.JCUnary) an_expr;
      if (un.getKind() == Kind.UNARY_MINUS) {
        new_expr = new UnaryExpression(Operator.UNARY_MINUS,
                                      parseExpr(un.getExpression()));
      } else if (un.getKind() == Kind.UNARY_PLUS) {
        new_expr = new UnaryExpression(Operator.UNARY_PLUS,
                                      parseExpr(un.getExpression()));
      } else if (un.getKind() == Kind.LOGICAL_COMPLEMENT) {
        new_expr = new UnaryExpression(Operator.NOT, parseExpr(un.getExpression()));
      } else {
        new_expr = new InformalExpression(an_expr.toString());
      }
      //end JCUnary
    } else if (an_expr instanceof JCTree.JCArrayAccess) {
      final JCTree.JCArrayAccess a = (JCTree.JCArrayAccess) an_expr;
      new_expr = new ArrayaccessExpression(parseExpr(a.indexed),
                                          parseExpr(a.index));
      //end JCArrayAccess
    } else if (an_expr instanceof JCTree.JCFieldAccess) {
      final JCTree.JCFieldAccess f = (JCTree.JCFieldAccess) an_expr;
      new_expr = new MemberaccessExpression(parseExpr(f.selected),
                                           new IdentifierExpression(f.name.toString()));
      //end JCFieldAccess
    } else if (an_expr instanceof JmlTree.JmlMethodInvocation) {
      
      final JmlTree.JmlMethodInvocation m = (JmlTree.JmlMethodInvocation) an_expr;
      final java.util.List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
      for (final JCTree.JCExpression e : m.getArguments()) {
        list.add(parseExpr(e));
      }
      if (m.token == JmlToken.BSOLD) {
        new_expr =
          new MethodcallExpression(new IdentifierExpression("old"), //$NON-NLS-1$
                                           list);
      } else {
        new_expr = new InformalExpression(m.toString());
      }
      //end JCMethodInvocation
    } else if (an_expr instanceof JCTree.JCMethodInvocation) {
      final JCTree.JCMethodInvocation m = (JCTree.JCMethodInvocation) an_expr;
      final java.util.List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
      for (final JCTree.JCExpression e : m.getArguments()) {
        list.add(parseExpr(e));
      }
      new_expr = new MethodcallExpression(parseExpr(m.getMethodSelect()),
                                         list);
    } else  if (an_expr instanceof JCTree.JCIdent) {
      new_expr = new IdentifierExpression(an_expr.toString());
      //end JCIdent
    } else if (an_expr instanceof JCTree.JCLiteral) {
      if (an_expr.getKind() == Kind.NULL_LITERAL) {
        new_expr = new Keyword(Keywords.NULL);
      } else if (an_expr.getKind() == Kind.BOOLEAN_LITERAL) {
        if (an_expr.toString().equals("true")) { //$NON-NLS-1$
          new_expr = new Keyword(Keywords.TRUE);
        } else if (an_expr.toString().equals("false")) { //$NON-NLS-1$
          new_expr = new Keyword(Keywords.FALSE);
        }
      } else {
        new_expr = new LiteralExpression(an_expr.toString());
      }
      //end JCLiteral
    } else if (an_expr instanceof JCTree.JCParens) {
      final JCTree.JCParens p = (JCTree.JCParens) an_expr;
      final BeetlzExpression e = parseExpr(p.expr);
      e.setParenthesised();
      new_expr = e;
    } else {
      if (an_expr == null) {
        new_expr = InformalExpression.EMPTY_COMMENT;
      } else {
        new_expr = new InformalExpression(an_expr.toString());
      }
    }

    return new_expr;
  }

  /**
   * Parse a feature specification.
   * @param some_specs specs to parse
   * @param a_pure is this feature pure
   * @param a_return_value return value of feature
   * @param an_encl_class_pure enclosing class
   * @return list specs clauses
   */
  private static List < Spec > parseFeatureSpecs(final MethodSpecs some_specs,
                                                 final boolean a_pure,
                                                 final SmartString a_return_value,
                                                 final boolean an_encl_class_pure) {
    final List < Spec > specCases = new Vector < Spec > ();

    for (final JmlTree.JmlSpecificationCase s : some_specs.cases.cases) {
      if (s.token == null || s.token == JmlToken.NORMAL_BEHAVIOR ||
          s.token == JmlToken.BEHAVIOR) {
        final List < BeetlzExpression > pre = new Vector < BeetlzExpression > ();
        final List < BeetlzExpression > post = new Vector < BeetlzExpression > ();
        final List < BeetlzExpression > frame = new Vector < BeetlzExpression > ();
        final String constant = null;
        FeatureType type;
        for (final JmlTree.JmlMethodClause c : s.clauses) {
          if (c instanceof JmlTree.JmlMethodClauseStoreRef) {
            final JmlTree.JmlMethodClauseStoreRef ass =
              (JmlTree.JmlMethodClauseStoreRef) c;
            //ignore captures and accesible clauses
            if(ass.token == JmlToken.ASSIGNABLE) {
              for (final JCTree t : ass.list) {
                if (t.getKind() == Kind.IDENTIFIER) {
                  frame.add(new IdentifierExpression(t.toString()));
                } else if (t.getKind() == Kind.OTHER && t.toString().equals(BConst.NOTHING)) {
                  frame.add(new Keyword(Keywords.NOTHING));
                } else if (t.getKind() == Kind.OTHER && t.toString().equals(BConst.EVERYTHING)) {
                  frame.add(new Keyword(Keywords.EVERYTHING));
                } else {
                  final int first = t.toString().indexOf("["); //$NON-NLS-1$
                  if (first != -1) {
                    frame.add(new IdentifierExpression(t.toString().substring(0, first)));
                  } else {
                    frame.add(new IdentifierExpression(t.toString()));
                  }
                }
              }
            }
          //end JmlAssignable
          } else if (c instanceof JmlTree.JmlMethodClauseExpr) {
            final JmlTree.JmlMethodClauseExpr expr = (JmlTree.JmlMethodClauseExpr) c;
            if (expr.token == JmlToken.REQUIRES) {
              final BeetlzExpression e = parseExpr(expr.expression);
              pre.addAll(splitBooleanExpressions(e));
            } else if (expr.token == JmlToken.ENSURES) {
              final BeetlzExpression e = parseExpr(expr.expression);
              post.addAll(splitBooleanExpressions(e));
            }
            //ignore all other clauses
          } //end JmlMethodClauseExpr

        }
        //Query or Command ?!
        if (a_return_value.equals(SmartString.getVoid())) {
          type = FeatureType.COMMAND;
          if (frame.size() == 0) {
            frame.add(new Keyword(Keywords.EVERYTHING));
          }
        //} else if (a_pure || (frame.size() == 1 && frame.get(0).
        } else if (a_pure || (frame.size() > 0 && 
            frame.get(0).compareToTyped(new Keyword(Keywords.NOTHING)) == 0)) {
          type = FeatureType.QUERY;
          frame.add(new Keyword(Keywords.NOTHING));
        } else {
          if (frame.size() == 0 && an_encl_class_pure) {
            type = FeatureType.QUERY;
            frame.add(new Keyword(Keywords.NOTHING));
          } else if (frame.size() == 0) {
            frame.add(new Keyword(Keywords.EVERYTHING));
            type = FeatureType.MIXED;
          } else {
            type = FeatureType.MIXED;
          }
        }
        specCases.add(new Spec(pre, post, frame, constant, type, ClassType.JAVA));
      } //end if normal behaviour
    }

    //No Specs:
    if (specCases.isEmpty()) {
      final List < BeetlzExpression > frame = new Vector < BeetlzExpression > ();
      FeatureType type;
      //Query or Command ?!
      if (a_return_value.equals(SmartString.getVoid())) {
        type = FeatureType.COMMAND;
        if (frame.size() == 0) {
          frame.add(new Keyword(Keywords.EVERYTHING));
        }
      } else if (a_pure || (frame.size() == 1 &&
          frame.get(0).equals(new Keyword(Keywords.NOTHING)))) {
        type = FeatureType.QUERY;
        frame.add(new Keyword(Keywords.NOTHING));
      } else {
        if (frame.size() == 0 && an_encl_class_pure) {
          type = FeatureType.QUERY;
          frame.add(new Keyword(Keywords.NOTHING));
        } else if (frame.size() == 0) {
          frame.add(new Keyword(Keywords.EVERYTHING));
          type = FeatureType.MIXED;
        } else {
          type = FeatureType.MIXED;
        }
      }
      specCases.add(new Spec(new Vector < BeetlzExpression > (),
                             new Vector < BeetlzExpression > (),
                             frame, null, type, ClassType.JAVA));
    }
    return specCases;

  }

  /**
   * Split an expression if necessary.
   * Expressions are split if they are AND expressions.
   * @param an_expr expression to split
   * @return split expression, put into a list
   */
  private static List < BeetlzExpression > splitBooleanExpressions(final BeetlzExpression an_expr) {
    final List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
    if (an_expr instanceof LogicalExpression) {
      final LogicalExpression and = (LogicalExpression) an_expr;
      if (and.getOperator() == Operator.AND) {
        list.addAll(splitBooleanExpressions(and.leftExpression()));
        list.addAll(splitBooleanExpressions(and.rightExpression()));
        return list;
      }
    }
    list.add(an_expr);
    return list;
  }

  /**
   * Parse a variable specs.
   * @param a_var variable specification
   * @param a_spec specs of the variable
   * @return specs
   */
  private static Spec parseVariableSpecs(final VarSymbol a_var,
                                         final FieldSpecs a_spec) {
    final List < BeetlzExpression > frame = new Vector < BeetlzExpression > ();
    frame.add(new Keyword(Keywords.NOTHING)); //all variables are pure...
    //Constant, initialiser is non-null?
    if (a_var.getConstantValue() != null) {
      return new Spec(new Vector < BeetlzExpression > (), new Vector < BeetlzExpression > (),
                      frame, a_var.getConstantValue().toString(),
                      FeatureType.QUERY, ClassType.JAVA);
    } else if (a_var.getModifiers().contains(Modifier.STATIC) &&
        a_var.getModifiers().contains(Modifier.FINAL)) {
      return new Spec(new Vector < BeetlzExpression > (), new Vector < BeetlzExpression > (),
                      frame, Spec.UNKNOWN_VALUE, FeatureType.QUERY, ClassType.JAVA);
    } else {
      return new Spec(new Vector < BeetlzExpression > (), new Vector < BeetlzExpression > (),
                      frame, null, FeatureType.QUERY, ClassType.JAVA);
    }
  }

  /**
   * Parse visibility speficiation.
   * @param a_var variable symbol to parse visibility from
   * @return visibility
   */
  private static VisibilityModifier parseSpecVisibility(final VarSymbol a_var) {
    for (final Attribute.Compound c : a_var.attributes_field) {
      if (c.toString().equals("@org.jmlspecs.annotation.SpecPublic")) { //$NON-NLS-1$
        return VisibilityModifier.PUBLIC;
      }
      if (c.toString().equals("@org.jmlspecs.annotation.SpecProtected")) { //$NON-NLS-1$
        return VisibilityModifier.PROTECTED;
      }
    }
    return null;
  }

  /**
   * Set the comment on a class.
   * @param the_cls class to set comments on
   * @param the_docs comments in string representation
   */
  private static void setComment(final ClassStructure the_cls, final String the_docs) {
    final List < String > about = new Vector < String > ();
    String author = ""; //$NON-NLS-1$
    String version = ""; //$NON-NLS-1$
    String all_else = ""; //$NON-NLS-1$
    final String[] parts = the_docs.split("\n"); //$NON-NLS-1$
    for (String s : parts) {
      s = s.trim();
      if (s.startsWith("@author")) { //$NON-NLS-1$
        author += s.replace("@author", ""); //$NON-NLS-1$ //$NON-NLS-2$
      } else if (s.startsWith("@version")) { //$NON-NLS-1$
        version += s.replace("@version", ""); //$NON-NLS-1$ //$NON-NLS-2$
      } else if (s.startsWith("@")) { //$NON-NLS-1$
        all_else += s;
      } else {
        about.add(s);
      }
    }
    the_cls.setComment(about, author, version, all_else);
  }
}
