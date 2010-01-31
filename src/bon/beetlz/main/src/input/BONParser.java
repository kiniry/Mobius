package input;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.EnumerationElement;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FeatureArgument;
import ie.ucd.bon.ast.FeatureName;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.FormalGeneric;
import ie.ucd.bon.ast.IndexClause;
import ie.ucd.bon.ast.Indexing;
import ie.ucd.bon.ast.SetConstant;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.ast.TypeMark;
import ie.ucd.bon.typechecker.BONST;
import ie.ucd.bon.ast.Expression;
import ie.ucd.bon.ast.BinaryExp;
import ie.ucd.bon.ast.UnaryExp;
import ie.ucd.bon.ast.KeywordConstant;
import ie.ucd.bon.ast.IntegerConstant;
import ie.ucd.bon.ast.CallExp;
import ie.ucd.bon.ast.BooleanConstant;
import ie.ucd.bon.ast.StringConstant;
import ie.ucd.bon.ast.UnqualifiedCall;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;

import log.CCLevel;
import log.CCLogRecord;
import logic.BeetlzExpression;
import logic.Operator;
import logic.BeetlzExpression.ArithmeticExpression;
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
import structure.ClassStructure;
import structure.FeatureStructure;
import structure.Invariant;
import structure.Signature;
import structure.Spec;
import structure.Visibility;
import utils.BConst;
import utils.BeetlzSourceLocation;
import utils.FeatureType;
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

/**
 * Parser for BON information from BONc data structures.
 * Takes BONc elements and puts the
 * required information into our own data structures.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public final class BONParser {
  
  private static List < BeetlzExpression > my_frame = new Vector < BeetlzExpression > ();
  private static Map < String , SmartString > my_parameters = new HashMap < String, SmartString > ();
  private static SmartString my_return_value = new SmartString();
  private static String my_featureName = "";
  private static String my_const = null;
  public enum Condition { PRE, POST, INV }  
  
  /**
   * Parse classes.
   * @param the_st symbol table
   * @param a_class class definition
   * @param the_clusters c cluster the class belongs to
   * @return parsed class
   */
  public static ClassStructure parseClass(final BONST the_st,
                                          final String a_className,
                                          final Collection<Cluster> the_clusters) {
    Clazz clazz = the_st.classes.get(a_className);
    final SortedSet  <  ClassModifier  > mod    = parseClassModifier(clazz);
    final Visibility vis                        = new Visibility(VisibilityModifier.PUBLIC);
    final List  < SmartString > generics   		  = new Vector < SmartString > ();
    final SortedSet < SmartString > interfaces  = new TreeSet < SmartString > ();
    Invariant inv                               = null;
    final List < SmartString > clus             = new Vector < SmartString > ();
    final TypeSmartString name = new TypeSmartString(a_className);
    final BeetlzSourceLocation src = new BeetlzSourceLocation(clazz.getReportingLocation());
    
    //Generics
    if (!clazz.generics.isEmpty()) {
      mod.add(ClassModifier.GENERIC);
      for (final FormalGeneric f : clazz.generics) {
        generics.add(getFormalGeneric(f));
      }
    }
    

    //Inheritance
    Collection<Type> superC = the_st.classInheritanceGraph.get(a_className); 
    if (superC != null) {
      for (final Type s : superC) {
        final boolean success = interfaces.add(getType(s));
        //TODO: check if bonc really does not support repeated inheritance
        if (!success) {
          Beetlz.getWaitingRecords().
          add(new CCLogRecord(CCLevel.JAVA_WARNING, null,
              String.format("Java does not support repeated inheritance. Repeated parent class %s in class %s will be ignored.", //$NON-NLS-1$
                  s, name)));
        }
      }
    }
    //Invariant
    Collection<Expression> invariants = Collections.emptyList();
    if (clazz.classInterface != null) {
      invariants = clazz.getClassInterface().getInvariant();
    } 
    inv = parseInvariant(invariants);
    
    //Cluster
    if (the_clusters != null && the_clusters.size() > 0) {
      Iterator iterator = the_clusters.iterator(); 
      while(iterator.hasNext()) {
        clus.add(new SmartString(((Cluster)iterator.next()).getName()));
      }
    }
    
    //Create class
    final ClassStructure parsedClass =
      new ClassStructure(ClassType.BON, mod, vis, generics, name,
          interfaces, clus, src);
    parseComments(parsedClass, the_st.indexing.get(clazz));
    parsedClass.setInvariant(inv);
    
    //Get the features
    if (clazz.classInterface != null) {

      for (final Feature feat : clazz.classInterface.features) {
        for (final FeatureSpecification fSpec : feat.featureSpecifications) {
          for (final FeatureName fName : fSpec.featureNames) {
            final FeatureStructure f = parseFeature(the_st, fSpec, fName.name, parsedClass);
            if (!Beetlz.getProfile().pureBon()) {
              if (f.getSimpleName().equals(BConst.MAKE) ||
                  f.getSimpleName().matches(BConst.MAKE + "[0-9]")) { //$NON-NLS-1$
                parsedClass.addConstructor(f);
                continue;
              }
            }
            parsedClass.addFeature(f);
          }
        }
      }
    }
    return parsedClass;
  }
  
  
  private static void parseComments(final ClassStructure cls, final Indexing index) {
    final int two = 2;
    final List < String > about = new Vector < String > ();
    String author = ""; //$NON-NLS-1$
    String version = ""; //$NON-NLS-1$
    String all_else = ""; //$NON-NLS-1$
    //Comments
    //final Indexing index = the_st.indexing.get(a_class);
    if (index != null) {
      for (final IndexClause i : index.getIndexes()) {
        if (i.getId().equals("about")) { //$NON-NLS-1$
          for (final String s : i.getIndexTerms()) {
            about.add(s.replace("\"", ""));  //$NON-NLS-1$//$NON-NLS-2$
          }
        } else if (i.getId().equals("author")) { //$NON-NLS-1$
          String a = ""; //$NON-NLS-1$
          for (final String s : i.getIndexTerms()) {
            a += s.replace("\"", "") + ", ";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
          }
          if (a.length() > two) {
            a = a.substring(0, a.length() - two);
          }
          author += a;
        } else if (i.getId().equals("version")) { //$NON-NLS-1$
          String v = ""; //$NON-NLS-1$
          for (final String s : i.getIndexTerms()) {
            v += s.replace("\"", "") + ", ";  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
          }
          if (v.length() > two) {
            v = v.substring(0, v.length() - two);
          }
          version += v;
        } else {
          String a = ""; //$NON-NLS-1$
          for (final String s : i.getIndexTerms()) {
            a += s.replace("\"", "" + ",");  //$NON-NLS-1$//$NON-NLS-2$ //$NON-NLS-3$
          }
          if (a.length() > two) {
            a = a.substring(0, a.length() - two);
          }
          all_else += a;
        }
      }
    }
    cls.setComment(about, author, version, all_else);
  }

  
  private static SortedSet < ClassModifier > parseClassModifier(Clazz a_class) {
    final SortedSet  <  ClassModifier  > mod    = new TreeSet < ClassModifier > ();
    switch(a_class.mod) {
      case DEFERRED: mod.add(ClassModifier.ABSTRACT); break;
      case EFFECTIVE: mod.add(ClassModifier.EFFECTIVE); break;
      case ROOT: mod.add(ClassModifier.ROOT); break;
    }
    //TODO: what does this mean?!
    if (a_class.getInterfaced()) mod.add(ClassModifier.INTERFACED);
    if (a_class.getPersistent()) mod.add(ClassModifier.PERSISTENT);
    if (a_class.getReused()) mod.add(ClassModifier.REUSED);
  
    return mod;
  }
  
  /**
   * Parse a feature.
   * @param a_feature feature to parse
   * @param a_encl_class enclosing class
   * @return parsed feature
   */
  private static FeatureStructure parseFeature(final BONST the_st,
      final FeatureSpecification fSpec,
      final String f_name,
      final ClassStructure a_encl_class) {
    
    //full feature
    final SortedSet < FeatureModifier > mod = new TreeSet < FeatureModifier > ();
    Visibility vis                          = new Visibility(VisibilityModifier.PUBLIC);
    String rename_class                     = null;
    String rename_feature                   = null;
    final FeatureSmartString name = new FeatureSmartString(f_name);
    final BeetlzSourceLocation src = new BeetlzSourceLocation(fSpec.getReportingLocation());
    
    
    //Modifier
    switch(fSpec.modifier) {
      case DEFERRED: mod.add(FeatureModifier.ABSTRACT); break;
      case REDEFINED: mod.add(FeatureModifier.REDEFINED); break;
      case EFFECTIVE: mod.add(FeatureModifier.EFFECTIVE); break;
    }
    
    //Visibility
    if (the_st.selectiveExportPrivateMap.get(fSpec)) {
      vis = new Visibility(VisibilityModifier.PRIVATE);
    } else if (!the_st.selectiveExportMap.get(fSpec).isEmpty()) {
      final List<String> exp = the_st.selectiveExportStringsMap.get(fSpec);
      if (exp.size() == 1 && exp.contains(a_encl_class.getSimpleName())) {
        vis = new Visibility(VisibilityModifier.PROTECTED);
      } else if (exp.size() == 1 && exp.contains(a_encl_class.getInnermostPackage().
          toString())) {
        vis = new Visibility(VisibilityModifier.PACKAGE_PRIVATE);
      } else {
        vis = new Visibility(VisibilityModifier.RESTRICTED);
      }
      final List < TypeSmartString > exports = new Vector < TypeSmartString > ();
      for (final String s : exp) {
        exports.add(new TypeSmartString(s));
      }
      vis.setExports(exports);
    }
    
    //Return type
    SmartString return_value = SmartString.getVoid(); //default is void
    final Map < String , SmartString > params = new HashMap < String, SmartString > ();
    if (fSpec.getHasType() != null) {
      return_value = getType(fSpec.getHasType().getType());
    }
    //Parameter
    for (final FeatureArgument a : fSpec.getArguments()) {
      params.put(a.getIdentifier(), getType(a.getType()));
    }

    final Spec spec = BONParser.parseFeatureSpecs(fSpec.getContracts().getPreconditions(), 
                                                  fSpec.getContracts().getPostconditions(), 
                                                  return_value, name.toString(), params);
    final List < Spec > specCases = new Vector < Spec > ();
    specCases.add(spec);
    final Signature sign = Signature.getBonSignature(return_value, params);
    
    //Renaming
    if (fSpec.getRenaming() != null) {
      rename_class = fSpec.getRenaming().getClassName().getName();
      rename_feature = fSpec.getRenaming().getFeatureName().getName();
    }
    //Client relations
    //TODO: find out why these are not covered, although we have shared associations,
    //maybe we don't this at all...
    if (fSpec.getHasType() != null && fSpec.getHasType().getMark().getMark() == TypeMark.Mark.SHAREDMARK) {
      a_encl_class.addSharedAssociation(return_value);
    }
    if (fSpec.getHasType() != null && fSpec.getHasType().getMark().getMark() == TypeMark.Mark.AGGREGATE) {
      a_encl_class.addAggregation(return_value);
    }
    return new FeatureStructure(mod, vis, name, sign, specCases, src, rename_class, rename_feature, a_encl_class);
  }

  
  /**
   * Parse an invariant.
   * @param the_invariant invariant clauses to parse.
   * @return parsed invariant
   */
  private static Invariant parseInvariant(Collection<Expression> the_invariant) {
    final List < BeetlzExpression > clauses = new Vector < BeetlzExpression > ();
    final List < BeetlzExpression > history = new Vector < BeetlzExpression > ();

    for (final Expression e: the_invariant) {
      final BeetlzExpression expr = parseExpr(e, Condition.INV);
      clauses.addAll(splitBooleanExpressions(expr));
    }
    return new Invariant(clauses, history);
  }
  
  private static BeetlzExpression parseExpr(Expression e, Condition c) {
    BeetlzExpression result = InformalExpression.EMPTY_COMMENT;
   
    if(e instanceof BinaryExp) {
      final BinaryExp bin = (BinaryExp) e;
      BinaryExp.Op op = bin.getOp();
      switch (op) {
        case EQUIV: result = new EquivalenceExpression(parseExpr(bin.getLeft(), c), 
            Operator.IFF, parseExpr(bin.getRight(), c)); break;
        case IMPLIES: result = new ImpliesExpression(parseExpr(bin.getLeft(), c), 
            parseExpr(bin.getRight(), c)); break;
        case GT: result = new RelationalExpression(parseExpr(bin.getLeft(), c), 
            Operator.GREATER, parseExpr(bin.getRight(), c)); break;    
        case GE: result = new RelationalExpression(parseExpr(bin.getLeft(), c), 
            Operator.GREATER_EQUAL, parseExpr(bin.getRight(), c)); break;
        case LT: result = new RelationalExpression(parseExpr(bin.getLeft(), c), 
            Operator.SMALLER, parseExpr(bin.getRight(), c)); break;                                 
        case LE: result = new RelationalExpression(parseExpr(bin.getLeft(), c), 
            Operator.SMALLER_EQUAL, parseExpr(bin.getRight(), c)); break;   
        
        case EQ: 
          BeetlzExpression right = parseExpr(bin.getRight(), c);
          BeetlzExpression left = parseExpr(bin.getLeft(), c);
          List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
          list.add(new IdentifierExpression(my_featureName));
          if(left.compareToTyped(new Keyword(Keywords.RESULT)) == 0 && 
              (right.compareToTyped(new MethodcallExpression(new IdentifierExpression("old"), list)) == 0)) {
            my_const = Spec.UNKNOWN_VALUE;    //constant
          } else if(left.compareToTyped(new Keyword(Keywords.RESULT)) == 0 && 
              (right instanceof LiteralExpression)) {
            my_const = ((LiteralExpression) right).toString();  //literal constant
          } else {
            result = new EqualityExpression(parseExpr(bin.getLeft(), c), 
                Operator.EQUAL, parseExpr(bin.getRight(), c)); break;
          }
          break;
        case NEQ: 
          BeetlzExpression rightt = parseExpr(bin.getRight(), c);
          BeetlzExpression leftt = parseExpr(bin.getLeft(), c);
          if(rightt.compareToTyped(new Keyword(Keywords.VOID)) == 0) {
            if(c == Condition.PRE) {
              for(String s: my_parameters.keySet()) {
                if(leftt.compareToTyped(new IdentifierExpression(s)) == 0) {
                  my_parameters.get(s).setNullity(Nullity.NON_NULL); //argument nullity, i.e. non-null
                }
              }
            } else if(c == Condition.POST) {
              if(leftt.compareToTyped(new Keyword(Keywords.RESULT)) == 0) {
                my_return_value.setNullity(Nullity.NON_NULL); //return value nullity, i.e. non-null
              }
            } else {
              //TODO: is this reachable at all?!
              result = new EqualityExpression(parseExpr(bin.getLeft(), c), 
                  Operator.NOT_EQUAL, parseExpr(bin.getRight(), c)); 
            }
          } else {
            result = new EqualityExpression(parseExpr(bin.getLeft(), c), 
                Operator.NOT_EQUAL, parseExpr(bin.getRight(), c)); 
          }
          break;                               
        case XOR: result = new LogicalExpression(parseExpr(bin.getLeft(), c), 
           Operator.XOR, parseExpr(bin.getRight(), c)); break;
        case OR: result = new LogicalExpression(parseExpr(bin.getLeft(), c), 
            Operator.OR, parseExpr(bin.getRight(), c)); break;
        case AND: result = new LogicalExpression(parseExpr(bin.getLeft(), c), 
            Operator.AND, parseExpr(bin.getRight(), c)); break;
        
        case MUL: result = new ArithmeticExpression(parseExpr(bin.getLeft(), c), 
            Operator.MULTIPLE, parseExpr(bin.getRight(), c)); break;
        case ADD: result = new ArithmeticExpression(parseExpr(bin.getLeft(), c), 
            Operator.PLUS, parseExpr(bin.getRight(), c)); break;
        case SUB: result = new ArithmeticExpression(parseExpr(bin.getLeft(), c), 
            Operator.MINUS, parseExpr(bin.getRight(), c)); break;   
        case DIV: result = new ArithmeticExpression(parseExpr(bin.getLeft(), c), 
            Operator.DIVIDE, parseExpr(bin.getRight(), c)); break;
        case MOD: result = new ArithmeticExpression(parseExpr(bin.getLeft(), c), 
            Operator.MODULO, parseExpr(bin.getRight(), c)); break;
        case INTDIV: result = new ArithmeticExpression(parseExpr(bin.getLeft(), c), 
            Operator.INT_DIVIDE, parseExpr(bin.getRight(), c)); break;                                  
        case POW: result = new ArithmeticExpression(parseExpr(bin.getLeft(), c), 
            Operator.POWER, parseExpr(bin.getRight(), c)); break;
            
        case NOTMEMBEROF: break;//TODO
        case HASTYPE: break;//TODO
        case MEMBEROF: break;//TODO
        default: System.out.println("unknown binary BON operator");break;
      }
    }//end bin op
    else if(e instanceof UnaryExp) {
      final UnaryExp un = (UnaryExp) e;
      UnaryExp.Op op = un.getOp();
      switch (op) {
        case OLD: 
          final java.util.List < BeetlzExpression > list = new Vector < BeetlzExpression > ();
          list.add(parseExpr(un.getExpression(), c));
          result = new MethodcallExpression(new IdentifierExpression("old"), //$NON-NLS-1$
            list); break;
        case DELTA:
          if(un.getExpression() instanceof CallExp) {
            my_frame.add(parseExpr(un.getExpression(), c));
          }
          else if(un.getExpression() instanceof SetConstant) {
            for(EnumerationElement call: ((SetConstant)un.getExpression()).getEnumerations()) {
              my_frame.add(parseExpr((Expression)call, c));
            }
          }
          else {
            //TODO: remove, after check in bonc that we've exhausted all possibilities
            System.err.println("WARNING unknown delta expression: " + e);
          }
          break; 
        case SUB: result = new UnaryExpression( 
            Operator.UNARY_MINUS, parseExpr(un.getExpression(), c)); break;
        case NOT: result = new UnaryExpression(
            Operator.NOT, parseExpr(un.getExpression(), c)); break;
        case ADD: result = new UnaryExpression( 
            Operator.UNARY_PLUS, parseExpr(un.getExpression(), c)); break;
        default: System.out.println("unknown unary BON operator");break;
      //TODO: remove, after check in bonc that we've exhausted all possibilities
      }
    }//end unary
    else if(e instanceof KeywordConstant) {
      KeywordConstant constant = (KeywordConstant)e;
      //System.err.println("keyword constant:" + e);
      switch (constant.getConstant()) {
      case RESULT: result = new Keyword(Keywords.RESULT); break;
      case VOID: result = new Keyword(Keywords.VOID); break;
      case CURRENT: result = new Keyword(Keywords.CURRENT); break;
      default: System.err.println("unknown BON keywordConstant " + c);break;
    //TODO: remove, after check in bonc that we've exhausted all possibilities
      }
    }
    else if(e instanceof IntegerConstant) {
      IntegerConstant constant = (IntegerConstant)e;
      result = new LiteralExpression(constant.getValue().toString());
    }
    else if(e instanceof BooleanConstant) {
      BooleanConstant constant = (BooleanConstant)e;
      if(constant.getValue().equals(Boolean.TRUE)) {
        result = new Keyword(Keywords.TRUE);
      }
      else if(constant.getValue().equals(Boolean.FALSE)) {
        result = new Keyword(Keywords.FALSE);
      }
      else 
         System.err.println("unknown BON boolean constant " + c);
    //TODO: remove, after check in bonc that we've exhausted all possibilities
    }
    else if(e instanceof StringConstant) {
      StringConstant constant = (StringConstant) e;
      result = new LiteralExpression(constant.getValue());
    }
    else if(e instanceof CallExp) {
      CallExp call = (CallExp)e;
      
      //get the arguments
      List < BeetlzExpression > args = new Vector < BeetlzExpression >();
      int size = call.getCallChain().size();
      if (size > 0) {
        for(Expression argument: call.getCallChain().get(size-1).getArgs()) {
          args.add(parseExpr(argument, c));
        }
        //now deal with the call chain recursively
        if (args.size() == 0) {
          result = parseMemberAccess(call.getCallChain());
        }
        else if(call.getQualifier() != null) {
          result = 
            new MethodcallExpression(new MemberaccessExpression(parseExpr(call.getQualifier(), c), 
                parseMemberAccess(call.getCallChain())), args);
        }
        else
          result = new MethodcallExpression(parseMemberAccess(call.getCallChain()), args);
      }
    }
    else {
      System.err.println("unknown expression: " + e); 
    //TODO: remove, after check in bonc that we've exhausted all possibilities
    }
    return result;
  }
  
 
  private static BeetlzExpression parseMemberAccess(List < UnqualifiedCall > a_callChain) {
    BeetlzExpression result = new IdentifierExpression("DUMMY");
    int size = a_callChain.size();
    if (size == 0) System.err.println("Error: empty call chain."); //TODO: make logger.sever message
    else if (size == 1) {
      //System.err.println("size 1: " + a_callChain.get(0).getId());
      result = new IdentifierExpression(a_callChain.get(0).getId());
    }
    else {
      //System.err.println("size else: " + a_callChain.get(size-1).getId());
      result = new MemberaccessExpression(parseMemberAccess(a_callChain.subList(0, size - 1)), 
          new IdentifierExpression(a_callChain.get(size-1).getId()));
    }
    return result;
  }
  
  
  /**
   * Parse feature specs.
   * @param a_pre precondition
   * @param a_post postcondition
   * @param a_return_value return value
   * @param a_feature feature name
   * @param the_params parameter
   * @return specs
   */
  public static Spec parseFeatureSpecs(final List<Expression> a_pre, 
		  final List<Expression> a_post, final SmartString a_return_value,
		  final String a_feature, final Map < String , SmartString > the_params) {
    
    List < BeetlzExpression > my_pre = new Vector < BeetlzExpression > ();
    List < BeetlzExpression > my_post = new Vector < BeetlzExpression > ();
    FeatureType my_type;
    my_parameters = the_params;
    my_return_value = a_return_value;
    my_featureName = a_feature;
    
    //reset data structures
    my_frame = new Vector < BeetlzExpression > ();
    my_const = null;
    
    for (Expression a_pre_exp : a_pre) {
      final BeetlzExpression e = parseExpr(a_pre_exp, Condition.PRE);
      
    //check if we have a meaningful expression, if not we had argument nullity expr.
    if(e.compareToTyped(InformalExpression.EMPTY_COMMENT) != 0)
      my_pre.addAll(splitBooleanExpressions(e));
 
    }
    
    for (Expression a_post_exp : a_post) {
      final BeetlzExpression e = parseExpr(a_post_exp, Condition.POST);
      
      //check if we have a meaningful expression, if not we had frame constraint, 
      //return nullity or constant
      if(e.compareToTyped(InformalExpression.EMPTY_COMMENT) != 0)
        my_post.addAll(splitBooleanExpressions(e));
    }
    
    //Query or Command ?!
    if (a_return_value.equals(SmartString.getVoid())) {
      my_type = FeatureType.COMMAND;
      if (my_frame.size() == 0) {
        my_frame.add(new Keyword(Keywords.EVERYTHING));
      }
    } else if (my_frame.size() == 0) {
      my_type = FeatureType.QUERY;
      my_frame.add(new Keyword(Keywords.NOTHING));
    } else {
      my_type = FeatureType.MIXED;
    }
     
    
    return new Spec(my_pre, my_post, my_frame,
        my_const, my_type, ClassType.BON);
   
  }
  

  /**
   * Parse type.
   * @param a_type type to parse
   * @return parsed type
   */
  private static SmartString getType(final Type a_type) {
    if (a_type.getIdentifier().equals("VOID")) {
      return SmartString.getVoid();
    }
    
    if (a_type.actualGenerics == null || a_type.actualGenerics.isEmpty()) {
      return new TypeSmartString(a_type.getIdentifier());
    }
    final SmartString name = new TypeSmartString(a_type.getIdentifier());
    final List < SmartString > params = new Vector < SmartString > ();
    for (final Type t : a_type.actualGenerics) {
      if (t.getIdentifier().equals("ANY")) { //$NON-NLS-1$
        params.add(WildcardSmartString.getBONWildcard());
        //TODO: include something with ANY
      } else {
        params.add(getType(t));
      }
    }
    return new ParametrizedSmartString(a_type.getIdentifier(), name, params);
 }
  
  

  /**
   * Parse generic parameters.
   * @param a_generic formal params
   * @return parsed generic parameter
   */
  private static SmartString getFormalGeneric(final FormalGeneric a_generic) {
    if (a_generic.getType() != null) {
      final List < SmartString > list = new Vector < SmartString > ();
      list.add(getType(a_generic.getType()));
      final String name = a_generic.getIdentifier() + " -> " +
      a_generic.getType().getIdentifier(); //$NON-NLS-1$
      return new GenericParameter(name, a_generic.getIdentifier(), list);
    }
    return new GenericParameter(a_generic.getIdentifier(), a_generic.getIdentifier(), null);
  }
  
  

  /**
   * Split a boolean expression based on AND.
   * @param an_expr expression to split
   * @return list of split expressions
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
  
  
}
