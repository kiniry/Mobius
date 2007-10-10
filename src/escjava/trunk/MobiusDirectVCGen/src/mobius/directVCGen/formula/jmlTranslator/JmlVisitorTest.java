package mobius.directVCGen.formula.jmlTranslator;

import java.util.HashSet;
import java.util.List;
import java.util.Properties;
import javafe.ast.*;
import mobius.directVCGen.formula.*;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.vcgen.struct.*;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.formula.annotation.Set;
import escjava.ast.ExprDeclPragma;
import escjava.ast.ExprModifierPragma;
import escjava.ast.ExprStmtPragma;
import escjava.ast.GenericVarDeclVec;
import escjava.ast.NaryExpr;
import escjava.ast.QuantifiedExpr;
import escjava.ast.ResExpr;
import escjava.ast.SetStmtPragma;
import escjava.ast.SimpleModifierPragma;
import escjava.ast.TagConstants;
import escjava.ast.TypeExpr;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.tc.Types;
import junit.framework.TestCase;


public class JmlVisitorTest extends TestCase {
  
  JmlVisitor fVisitor;
  JmlExprToFormula ftranslator;
  Properties fProp = new Properties();
  String expectedString = "";
  boolean expectedBool = true;
  Term expectedTerm = null;
  Term evaluatedTerm = null;
  LiteralExpr left = null;
  LiteralExpr right = null;
  FieldAccess xFieldAccessExprInt = null;
  FieldAccess xFieldAccessExprRef = null;
  FieldAccess yFieldAccessExprInt = null;
  FieldAccess yFieldAccessExprRef = null;
  FieldAccess arrayFieldAccessIndexExpr = null;
  VariableAccess indexLocalVarAccessExpr = null; //index i of array a
  VariableAccess xVariableAccessExprInt = null;
  VariableAccess xLocalVarAccessExprInt = null;
  VariableAccess arrayVarAccessExpr;
  LocalVarDecl indexLocalDeclInt = null;
  LocalVarDecl xLocalDeclInt = null;
  
  TypeName typeTwo = null;
  FieldDecl xFieldDeclInt = null;
  FieldDecl yFieldDeclInt = null;
  FieldDecl xFieldDeclRef = null;
  FieldDecl yFieldDeclRef = null;
  FieldDecl arrayFieldDeclInt = null; 
  ClassDecl twoClassDecl = null;
  ClassDecl oneClassDecl = null;
  
  ExprObjectDesignator xFieldODExpr = null;
  ExprObjectDesignator yFieldODExpr = null;
  ExprObjectDesignator arrayFieldODExpr = null;
  
  
  BinaryExpr binExpr = null;
  BinaryExpr binExpr1 = null;
  BinaryExpr binExpr2 = null;
  BinaryExpr binExpr3 = null;
  BinaryExpr binExpr4 = null;
  BinaryExpr binExpr5 = null;
  BinaryExpr binExpr6 = null;
  LiteralExpr sevenExprInt;
  LiteralExpr fourExprInt;
  LiteralExpr zeroExprInt;
  UnaryExpr sevenExprIntNeg;
  UnaryExpr fourExprIntNeg;
  LiteralExpr sevenExprReal;
  LiteralExpr fourExprReal;
  LiteralExpr zeroExprReal;
  UnaryExpr sevenExprRealNeg;
  UnaryExpr fourExprRealNeg;
  ArrayRefExpr arrayRefExpr = null;

  
  Term expTerm1;
  Term expTerm2;
  Term expTerm3;
  Term expTerm4;
  Term expTerm5;
  Term expTerm6;
  
  
  Term fourTermInt; 
  Term zeroTermInt; 
  Term fourTermIntNeg; 
  Term sevenTermInt; 
  Term fourTermReal; 
  Term zeroTermReal; 
  Term fourTermRealNeg;
  Term sevenTermReal;
  Term sevenTermIntNeg;
  Term sevenTermRealNeg;
  QuantVariableRef indexLocalVarAccessTerm;
  QuantVariableRef xLocalVarAccessTerm;
  Term xFieldAccessTermInt;
  Term xOldFieldAccessTermInt;
  Term xFieldAccessTermReal;
  Term xFieldAccessTermRef;
  Term yFieldAccessTermInt;
  Term yFieldAccessTermReal;
  Term yFieldAccessTermRef;
  Term arrayFieldAccessIndexTerm; //int[] a; mit index i
  ArrayInit arrayInit;
  
  int loc1 = 1000001;
  int loc2 = 1000001;

  
  public void setUp() throws Exception {
    fVisitor = new JmlVisitor();
    ftranslator = new JmlExprToFormula(fVisitor);
  
    fProp = new Properties();
    fProp.put("pred", Boolean.TRUE);
    fProp.put("old", Boolean.FALSE);
    fProp.put("assignableSet", new HashSet<QuantVariableRef[]>());
    fProp.put("freshSet", new HashSet<Term>());
    fProp.put("nothing", Boolean.FALSE);
    fProp.put("interesting", Boolean.FALSE);
    fProp.put("firstPost", Boolean.TRUE);
    fProp.put("routinebegin", Boolean.TRUE);  
    fProp.put("quantifier", Boolean.FALSE);
    fProp.put("quantVars", new HashSet<QuantVariable>());
    fProp.put("isHelper", Boolean.FALSE);
    fProp.put("fresh", Boolean.FALSE);
    fProp.put("unaryOp", 0);
    fProp.put("interesting", Boolean.TRUE);
    fProp.put("doSubsetChecking", Boolean.TRUE);
    fProp.put("subsetCheckingSet", new HashSet<FieldAccess>());

    
   
//*********************** Decls *****************************************************    
    
    twoClassDecl = ClassDecl.make(0, null, Identifier.intern("Two"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
    fProp.put("classId", twoClassDecl.id);
    oneClassDecl = ClassDecl.make(0, null, Identifier.intern("One"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
    xFieldDeclInt = FieldDecl.make(0, null, Identifier.intern("x"), JavafePrimitiveType.make(TagConstants.INTTYPE, loc1), loc1, null, 0);
    yFieldDeclInt = FieldDecl.make(0, null, Identifier.intern("y"), JavafePrimitiveType.make(TagConstants.INTTYPE, loc1), loc2, null, 0);
    xFieldDeclRef = FieldDecl.make(0, null, Identifier.intern("x"), TypeName.make(Name.make("Two", loc1)), loc2, null, 0);
    yFieldDeclRef = FieldDecl.make(0, null, Identifier.intern("y"), TypeName.make(Name.make("Two", loc1)), loc2, null, 0);
    xFieldDeclRef.parent = twoClassDecl;
    yFieldDeclRef.parent = twoClassDecl;
    xFieldDeclInt.parent = twoClassDecl;
    yFieldDeclInt.parent = twoClassDecl;
    xLocalDeclInt = LocalVarDecl.make(0, null, Identifier.intern("x"), JavafePrimitiveType.make(TagConstants.INTTYPE, 0), 1000001, null, 0);
    
    xFieldODExpr = ExprObjectDesignator.make(loc2, ThisExpr.make(null, loc1));
    yFieldODExpr = ExprObjectDesignator.make(loc1, ThisExpr.make(null, loc2));    
    
//*********************** Terms *****************************************************
   
    fourTermInt = Num.value((Integer) 4);
    zeroTermInt = Num.value((Integer) 0);
    fourTermIntNeg = Num.value((Integer) (-4)); 
    sevenTermInt = Num.value((Integer) 7);
    fourTermReal = Num.value((Double) 4.0);
    zeroTermReal = Num.value((Double) 0.0);
    fourTermRealNeg = Num.value((Double) (-4.0)); 
    sevenTermReal = Num.value((Double) 7.0);
    sevenTermIntNeg = Num.value((Integer) (-7));
    sevenTermRealNeg = Num.value((Double) (-7.0));    
    
//    xFieldAccessTermInt = Heap.select(Heap.var, Ref.varThis, Expression.var(xFieldDeclInt));
//    xOldFieldAccessTermInt = Heap.select(Heap.varPre, Ref.varThis, Expression.var(xFieldDeclInt));
//    yFieldAccessTermInt = Heap.select(Heap.var, Ref.varThis, Expression.var(yFieldDeclInt));
//    xFieldAccessTermRef = Heap.select(Heap.var, Ref.varThis, Expression.var(xFieldDeclRef));
//    yFieldAccessTermRef = Heap.select(Heap.var, Ref.varThis, Expression.var(yFieldDeclRef));
    xLocalVarAccessExprInt = VariableAccess.make(Identifier.intern("x"), loc1, xLocalDeclInt);
    xLocalVarAccessTerm =  Expression.rvar(xLocalVarAccessExprInt.decl);

    
//*********************** Exprs *****************************************************    
    
    sevenExprInt = LiteralExpr.make(TagConstants.INTLIT, 7, loc1);
    fourExprInt = LiteralExpr.make(TagConstants.INTLIT, 4, loc2);
    zeroExprInt = LiteralExpr.make(TagConstants.INTLIT, 0, loc2);
    sevenExprReal = LiteralExpr.make(TagConstants.DOUBLELIT , 7, loc1);
    fourExprReal = LiteralExpr.make(TagConstants.DOUBLELIT, 4, loc2);
    zeroExprReal = LiteralExpr.make(TagConstants.DOUBLELIT, 0, loc2);
    sevenExprIntNeg = UnaryExpr.make(88, sevenExprInt, loc1);
    fourExprIntNeg = UnaryExpr.make(88, fourExprInt, loc2);
    sevenExprRealNeg = UnaryExpr.make(88, sevenExprReal, loc1);
    fourExprRealNeg = UnaryExpr.make(88, fourExprReal, loc2);
    
    
    xFieldAccessExprInt = FieldAccess.make(xFieldODExpr, Identifier.intern("x"), loc1);
    xFieldAccessExprInt.decl = xFieldDeclInt;
    yFieldAccessExprInt = FieldAccess.make(yFieldODExpr, Identifier.intern("x"), loc2);
    yFieldAccessExprInt.decl = yFieldDeclInt;
    
    xFieldAccessExprRef = FieldAccess.make(xFieldODExpr, Identifier.intern("x"), loc1);
    xFieldAccessExprRef.decl = xFieldDeclRef;
    yFieldAccessExprRef = FieldAccess.make(yFieldODExpr, Identifier.intern("y"), loc1);
    yFieldAccessExprRef.decl = yFieldDeclRef;
    
    arrayFieldAccessIndexExpr = FieldAccess.make(arrayFieldODExpr, Identifier.intern("a"), 0);
    xVariableAccessExprInt = VariableAccess.make(Identifier.intern("x"), 0 , xLocalDeclInt);
       
    arrayFieldAccessIndexTerm = doArrayAccessAI();
  }
  
 
  private Term doArrayAccessAI() { // int[] a; and index i
    
    //*************Expression************************
    arrayFieldODExpr = ExprObjectDesignator.make(loc1, ThisExpr.make(null, loc2));
    arrayInit = ArrayInit.make(null, 0, 0);
    arrayFieldDeclInt = FieldDecl.make(0, null, Identifier.intern("a"), ArrayType.make(JavafePrimitiveType.make(TagConstants.INTTYPE, 0), 0), 0, arrayInit, 0);
    arrayFieldDeclInt.parent = twoClassDecl;
    arrayFieldAccessIndexExpr = FieldAccess.make(arrayFieldODExpr, Identifier.intern("a"), 0);
    arrayFieldAccessIndexExpr.decl = arrayFieldDeclInt;
    indexLocalDeclInt = LocalVarDecl.make(0, null, Identifier.intern("i"), JavafePrimitiveType.make(TagConstants.INTTYPE, 0), 1000001, null, 0);
    indexLocalVarAccessExpr = VariableAccess.make(Identifier.intern("i"), 0 , indexLocalDeclInt);
    
    arrayRefExpr = ArrayRefExpr.make(arrayFieldAccessIndexExpr, indexLocalVarAccessExpr, 0, 0);
    final Object[] dec = new Object[3];
    dec[0] = JavafePrimitiveType.make(TagConstants.INTTYPE, 0);
    dec[1] = JavafePrimitiveType.make(TagConstants.INTTYPE, 0);
    dec[2] = JavafePrimitiveType.make(TagConstants.INTTYPE, 0);
    arrayRefExpr.setDecorations(dec);

    //***************Term****************************
    final Term obj = (Term) arrayFieldAccessIndexExpr.od.accept(fVisitor, fProp);
    final QuantVariable var = (QuantVariable) Expression.var(arrayFieldAccessIndexExpr.decl);
    final Term array = Heap.select(Heap.var, obj, var, Num.sortInt);
    arrayVarAccessExpr = VariableAccess.make(Identifier.intern("i"), loc1, indexLocalDeclInt);
    indexLocalVarAccessTerm =  Expression.rvar(arrayVarAccessExpr.decl);
    
    return Heap.selectArray(Heap.var, array, indexLocalVarAccessTerm, Num.sortInt);
  }
  
  
  /**
   * Testing of JmlExprToFormula.eq(Expr, Object)
   *
   */
  public void testEq() {    
    
    // 4 == ((7*0)+4)
    fProp.put("pred", Boolean.TRUE);
    expTerm1 = Logic.equals(fourTermInt, Num.add(Num.mul(sevenTermInt, zeroTermInt), fourTermInt));
    binExpr1 = javafe.ast.BinaryExpr.make(TagConstants.STAR, sevenExprInt, zeroExprInt, 0);
    binExpr1 = javafe.ast.BinaryExpr.make(TagConstants.ADD, binExpr1, fourExprInt, 0);
    binExpr1 = javafe.ast.BinaryExpr.make(TagConstants.EQ, fourExprInt, binExpr1, 0);
    assertEquals(expTerm1.toString(), fVisitor.visitBinaryExpr(binExpr1, fProp).toString());
    
    // 4 == ((7*0)+4)
    fProp.put("pred", Boolean.FALSE);
    expTerm1 = Bool.equals(fourTermInt, Num.add(Num.mul(sevenTermInt, zeroTermInt), fourTermInt)); 
    assertEquals(expTerm1.toString(), fVisitor.visitBinaryExpr(binExpr1, fProp).toString());
   
    //  x == 4
    fProp.put("pred", Boolean.FALSE);
    binExpr2 = javafe.ast.BinaryExpr.make(TagConstants.EQ, xFieldAccessExprInt, fourExprInt,  0); 
    expTerm2 = Bool.equals(xFieldAccessTermInt, fourTermInt); 
    assertEquals(expTerm2.toString(), fVisitor.visitBinaryExpr(binExpr2, fProp).toString());
    
    //  (x > 7 ) == (4 == y)
    fProp.put("pred", Boolean.FALSE);
    binExpr1 = javafe.ast.BinaryExpr.make(TagConstants.GT, xFieldAccessExprInt, sevenExprInt, loc1);
    binExpr2 = javafe.ast.BinaryExpr.make(TagConstants.EQ, fourExprInt, yFieldAccessExprInt, loc2);
    binExpr = javafe.ast.BinaryExpr.make(TagConstants.EQ, binExpr1, binExpr2, loc2);
    expTerm2 = Bool.equals(Bool.gt(xFieldAccessTermInt, sevenTermInt), Bool.equals(fourTermInt, yFieldAccessTermInt)); 
    String ow =  fVisitor.visitBinaryExpr(binExpr2, fProp).toString();
    String tw = expTerm2.toString();
    assertEquals(expTerm2.toString(), fVisitor.visitBinaryExpr(binExpr, fProp).toString());
    // the same with pred = true
    fProp.put("pred", Boolean.TRUE);
    expTerm2 = Logic.equals(Bool.gt(xFieldAccessTermInt, sevenTermInt), Bool.equals(fourTermInt, yFieldAccessTermInt)); 
    assertEquals(expTerm2.toString(), fVisitor.visitBinaryExpr(binExpr, fProp).toString());  
    
    //  -4 != -7
    fProp.put("pred", Boolean.FALSE);
    binExpr2 = javafe.ast.BinaryExpr.make(TagConstants.NE, fourExprIntNeg, sevenExprIntNeg,  0); 
    expTerm2 = Bool.not(Bool.equals(fourTermIntNeg, sevenTermIntNeg)); 
    assertEquals(expTerm2.toString(), fVisitor.visitBinaryExpr(binExpr2, fProp).toString());
  }
  
  /**
   * Testing of \fresh JML feature in JmlExprToFormula.freshExpression(NaryExpr, Object)
   */
  public void testVisitNaryExpr() { //fresh=NaryExpr with tag = TagConstant.Fresh

    //############# Expression ###########################
    //  \fresh (this.x, this.y) whereas this = Two and x, y of type Two
    ExprVec freshVarVec = ExprVec.make();
    freshVarVec.addElement(xFieldAccessExprRef);
    freshVarVec.addElement(yFieldAccessExprRef);    
    NaryExpr naryFreshExpr = NaryExpr.make(0, 0, TagConstants.FRESH, Identifier.intern(""), freshVarVec);
    
    evaluatedTerm = (Term) fVisitor.visitNaryExpr(naryFreshExpr, fProp);
    //***************Term**********************************
    expTerm1 = Logic.not(Logic.equalsNull(Expression.rvar((GenericVarDecl) xFieldDeclRef)));
    expTerm2 = Logic.not(Logic.isAlive(Heap.varPre, Expression.rvar((GenericVarDecl) xFieldDeclRef)));
    expTerm3 = Logic.isAlive(Heap.var, Expression.rvar((GenericVarDecl) xFieldDeclRef));
    expTerm4 = Logic.and(Logic.and(expTerm1, expTerm2), expTerm3);
    
    expTerm1 = Logic.not(Logic.equalsNull(Expression.rvar((GenericVarDecl) yFieldDeclRef)));
    expTerm2 = Logic.not(Logic.isAlive(Heap.varPre, Expression.rvar((GenericVarDecl) yFieldDeclRef)));
    expTerm3 = Logic.isAlive(Heap.var, Expression.rvar((GenericVarDecl) yFieldDeclRef));
    expTerm5 = Logic.and(Logic.and(expTerm1, expTerm2), expTerm3);
    expectedTerm = Logic.and(expTerm5, expTerm4);
    //***************Test***********************************    
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());  

   
  }
  
  
  public void testBinaryExpr() { 
    //############# Expression ###########################
    // typeof(true) == type(boolean)
    final TypeExpr type1 = TypeExpr.make(0, 0, JavafePrimitiveType.make(TagConstants.BOOLEANTYPE, 0));
    final TypeExpr type2 = TypeExpr.make(0, 0, JavafePrimitiveType.make(TagConstants.BOOLEANTYPE, 0));
    binExpr = javafe.ast.BinaryExpr.make(TagConstants.EQ, type1, type2, loc1);
    evaluatedTerm = (Term) fVisitor.visitBinaryExpr(binExpr, fProp);
    //***************Term**********************************
    String name = Types.printName(((TypeExpr)type1).type);
    Term type1Term = Expression.rvar(name, Type.sort);
    expectedTerm =  Logic.equals(type1Term, type1Term);
    //***************Test***********************************
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());

   
    //############# Expression ###########################
    // old(x) >= x;
    ExprVec exprVec = ExprVec.make(new Expr[]{xFieldAccessExprInt});
    NaryExpr naryE = NaryExpr.make(0, 0, TagConstants.PRE, Identifier.intern(""), exprVec);
    binExpr = javafe.ast.BinaryExpr.make(TagConstants.GE, naryE, xFieldAccessExprInt, loc1);
    evaluatedTerm = (Term) fVisitor.visitBinaryExpr(binExpr, fProp);
    //***************Term**********************************
    expectedTerm =  Logic.ge(xOldFieldAccessTermInt, xFieldAccessTermInt);
    //***************Test***********************************
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());
  }
  

  
  
  /**
   * Testing array access (array:a, index:i)
   */
  public void testVisitArrayRefExpr() {
    //*************Test************************
    assertEquals(arrayFieldAccessIndexTerm.toString(), fVisitor.visitArrayRefExpr(arrayRefExpr, fProp).toString());
  }
  
  /**
   * Testing of forAll and Exists quantors
   */
  public void testQuantifier() {
    final GenericVarDeclVec qvarsExpr = GenericVarDeclVec.make();
    QuantVariable[] qvarsTerm;
    BinaryExpr rangeExpr;
    Term rangeTerm;
    BinaryExpr expr;
    Term exprTerm;
    QuantifiedExpr qExpr; 
    Term qTerm;

    //############# Expression ###########################
    //forall int i; i < 4 ; a[i] < 7;
    qvarsExpr.removeAllElements();
    qvarsExpr.addElement(indexLocalDeclInt);
    rangeExpr = BinaryExpr.make(TagConstants.LT, indexLocalVarAccessExpr, fourExprInt, loc1);
    expr = BinaryExpr.make(TagConstants.IMPLIES, rangeExpr, BinaryExpr.make(TagConstants.LT, arrayRefExpr, sevenExprInt, loc2), loc1); //PS: expr = range -> expr
    qExpr = QuantifiedExpr.make(0, 0, TagConstants.FORALL, qvarsExpr, rangeExpr, expr, null, null); 
    //***************Term**********************************
    qvarsTerm =  new QuantVariable[1];
    qvarsTerm[0] = indexLocalVarAccessTerm.qvar;
    rangeTerm = Logic.lt(indexLocalVarAccessTerm, fourTermInt);
    exprTerm = Logic.implies(rangeTerm, Logic.lt(arrayFieldAccessIndexTerm, sevenTermInt));
    qTerm = Logic.forall(qvarsTerm, exprTerm);
    //***************Test***********************************
    assertEquals(qTerm.toString(), fVisitor.visitQuantifiedExpr(qExpr, fProp).toString());

  
    
    //############# Expression ###########################
    //forall int i, int x; i < 4 && x < 7 ; a[i] < 7 && a[i] + x > 0;
    qvarsExpr.removeAllElements();
    qvarsExpr.addElement(indexLocalDeclInt);
    qvarsExpr.addElement(xLocalDeclInt);
    rangeExpr = BinaryExpr.make(TagConstants.AND, BinaryExpr.make(TagConstants.LT, indexLocalVarAccessExpr, fourExprInt, loc1), BinaryExpr.make(TagConstants.LT, xVariableAccessExprInt, sevenExprInt, loc1), loc2);
    expr = BinaryExpr.make(TagConstants.IMPLIES, rangeExpr, BinaryExpr.make(TagConstants.AND, BinaryExpr.make(TagConstants.LT, arrayRefExpr, sevenExprInt, loc2), BinaryExpr.make(TagConstants.GT, BinaryExpr.make(TagConstants.ADD, arrayRefExpr, xVariableAccessExprInt, loc1), zeroExprInt, loc1), loc2), loc1); //PS: expr = range -> expr
    qExpr = QuantifiedExpr.make(0, 0, TagConstants.FORALL, qvarsExpr, rangeExpr, expr, null, null); 
    //***************Term**********************************
    qvarsTerm =  new QuantVariable[2];
    qvarsTerm[0] = indexLocalVarAccessTerm.qvar;
    qvarsTerm[1] = xLocalVarAccessTerm.qvar;
    rangeTerm = Logic.and(Logic.lt(indexLocalVarAccessTerm, fourTermInt), Logic.lt(xLocalVarAccessTerm, sevenTermInt));
    exprTerm = Logic.implies(rangeTerm, Logic.and(Logic.lt(arrayFieldAccessIndexTerm, sevenTermInt), Logic.gt(Num.add(arrayFieldAccessIndexTerm, xLocalVarAccessTerm), zeroTermInt)));
    qTerm = Logic.forall(qvarsTerm, exprTerm);
    //***************Test***********************************
    assertEquals(qTerm.toString(), fVisitor.visitQuantifiedExpr(qExpr, fProp).toString());

  
    //############# Expression ###########################
    //exists int i; i > 0; a[i] !=  7
    qvarsExpr.removeAllElements();
    qvarsExpr.addElement(indexLocalDeclInt);
    rangeExpr = BinaryExpr.make(TagConstants.GT, indexLocalVarAccessExpr, zeroExprInt, loc1);
    expr = BinaryExpr.make(TagConstants.IMPLIES, rangeExpr, BinaryExpr.make(TagConstants.NE, arrayRefExpr, sevenExprInt, loc2), loc1); //PS: expr = range -> expr
    qExpr = QuantifiedExpr.make(0, 0, TagConstants.EXISTS, qvarsExpr, rangeExpr, expr, null, null); 
    //***************Term**********************************
    qvarsTerm =  new QuantVariable[1];
    qvarsTerm[0] = indexLocalVarAccessTerm.qvar;
    rangeTerm = Logic.gt(indexLocalVarAccessTerm, zeroTermInt);
    exprTerm = Logic.implies(rangeTerm, Logic.not(Logic.equals(arrayFieldAccessIndexTerm, sevenTermInt)));
    qTerm = Logic.exists(qvarsTerm, exprTerm);
    //***************Test***********************************
    assertEquals(qTerm.toString(), fVisitor.visitQuantifiedExpr(qExpr, fProp).toString());

  
    
    //############# Expression ###########################
    //exists int i, x; i <= 7; a[i] == x or a[i] < 7;
    qvarsExpr.removeAllElements();
    qvarsExpr.addElement(indexLocalDeclInt);
    qvarsExpr.addElement(xLocalDeclInt);
    rangeExpr = BinaryExpr.make(TagConstants.LE, indexLocalVarAccessExpr, sevenExprInt, loc1);
    expr = BinaryExpr.make(TagConstants.IMPLIES, rangeExpr,  
                           BinaryExpr.make(TagConstants.OR, 
                                           BinaryExpr.make(TagConstants.EQ, arrayRefExpr, xLocalVarAccessExprInt, loc1), 
                                           BinaryExpr.make(TagConstants.LT, arrayRefExpr, sevenExprInt, loc2), loc1), loc1); //PS: expr = range -> expr
    qExpr = QuantifiedExpr.make(0, 0, TagConstants.EXISTS, qvarsExpr, rangeExpr, expr, null, null); 
    //***************Term**********************************
    qvarsTerm =  new QuantVariable[2];
    qvarsTerm[0] = indexLocalVarAccessTerm.qvar;
    qvarsTerm[1] = xLocalVarAccessTerm.qvar;
    rangeTerm = Logic.le(indexLocalVarAccessTerm, sevenTermInt);
    exprTerm = Logic.implies(rangeTerm, Logic.or(Logic.equals(arrayFieldAccessIndexTerm, xLocalVarAccessTerm), Logic.lt(arrayFieldAccessIndexTerm, sevenTermInt)));
    qTerm = Logic.exists(qvarsTerm, exprTerm);
    //***************Test***********************************
    assertEquals(qTerm.toString(), fVisitor.visitQuantifiedExpr(qExpr, fProp).toString());

  }
  
  /**
   * Testing of Initially, Invariant and Constraint features
   */
  public void testVisitExprDeclPragma() { 
    ExprDeclPragma x;
    
    //############# Expression ###########################
    // initially x != 7;
    binExpr = BinaryExpr.make(TagConstants.NE, xFieldAccessExprInt, sevenExprInt, loc2);
    x = ExprDeclPragma.make(TagConstants.INITIALLY, binExpr, 0, loc1);
    x.parent = twoClassDecl;
    fVisitor.visitExprDeclPragma(x, fProp);
    evaluatedTerm = (Term) fProp.get("initiallyFOL");
    //***************Term**********************************
    expectedTerm = Logic.not(Logic.equals(xFieldAccessTermInt, sevenTermInt));
    //*************Test************************
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());

    
    //############# Expression ###########################
    // invariant x <= 4;
    binExpr = BinaryExpr.make(TagConstants.LE, xFieldAccessExprInt, fourExprInt, loc2);
    x = ExprDeclPragma.make(TagConstants.INVARIANT, binExpr, 0, loc1);
    x.parent = twoClassDecl;
    fVisitor.visitExprDeclPragma(x, fProp);
    evaluatedTerm = (Term) Lookup.invariants.get(twoClassDecl);
    //***************Term**********************************
    expectedTerm = Logic.le(xFieldAccessTermInt, fourTermInt);
    //*************Test************************
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());

    
    
    //############# Expression ###########################
    // constraint y > 0;
    binExpr = BinaryExpr.make(TagConstants.GT, yFieldAccessExprInt, zeroExprInt, loc2);
    x = ExprDeclPragma.make(TagConstants.CONSTRAINT, binExpr, 0, loc1);
    x.parent = twoClassDecl;
    fVisitor.visitExprDeclPragma(x, fProp);
    evaluatedTerm = (Term) Lookup.constraints.get(twoClassDecl);
    //***************Term**********************************
    expectedTerm = Logic.gt(yFieldAccessTermInt, zeroTermInt);
    //*************Test************************
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());
    
  }
  
  /**
   * Testing of Assert, Assume, Maintaining, Ghost and Set features
   */
  public void testVisitBlockStmt() { 
    fProp.put("routinebegin", Boolean.FALSE); 
    ExprStmtPragma jmlStmt;
    SkipStmt javaSkipStmt;
    WhileStmt javaWhileStmt;
    StmtVec vec;
    BlockStmt allStmts;
    List<AAnnotation> list;
    Term assumeTerm;
    
    // ############# Expression ###########################
    // assume x > 0;
    // skip stmt;
    binExpr = BinaryExpr.make(TagConstants.GT, xFieldAccessExprInt, zeroExprInt, loc2);
    jmlStmt = ExprStmtPragma.make(TagConstants.ASSUME, binExpr, null, loc2); 
    javaSkipStmt = SkipStmt.make(loc2); 
    vec = StmtVec.make(new Stmt[] {jmlStmt, javaSkipStmt});
    allStmts = BlockStmt.make(vec, 0, 0);
    fVisitor.visitBlockStmt(allStmts, fProp);
    list =  AnnotationDecoration.inst.getAnnotPre((ASTNode) javaSkipStmt);
    assumeTerm = list.get(0).formula;
    //***************Term**********************************
    expectedTerm = Logic.gt(xFieldAccessTermInt, zeroTermInt);
    //*************Test************************
    assertEquals(expectedTerm.toString(), assumeTerm.toString());
    
    
    // ############# Expression ###########################
    // assert x > 0;
    // skip stmt;
    list.clear();
    binExpr = BinaryExpr.make(TagConstants.GT, xFieldAccessExprInt, zeroExprInt, loc2);
    jmlStmt = ExprStmtPragma.make(TagConstants.ASSERT, binExpr, null, loc2); 
    javaSkipStmt = SkipStmt.make(loc2); 
    vec = StmtVec.make(new Stmt[] {jmlStmt, javaSkipStmt});
    allStmts = BlockStmt.make(vec, 0, 0);
    fVisitor.visitBlockStmt(allStmts, fProp);
    list =  AnnotationDecoration.inst.getAnnotPre((ASTNode) javaSkipStmt);
    assumeTerm = list.get(0).formula;
    //***************Term**********************************
    expectedTerm = Logic.gt(xFieldAccessTermInt, zeroTermInt);
    //*************Test************************
    assertEquals(expectedTerm.toString(), assumeTerm.toString());
    
    
    //############# Expression ###########################
    // maintaining x > 7;
    // whileStmt;
    list.clear();
    binExpr = BinaryExpr.make(TagConstants.GT, xFieldAccessExprInt, sevenExprInt, loc2);
    jmlStmt = ExprStmtPragma.make(TagConstants.MAINTAINING, binExpr, null, loc2); 
    javaWhileStmt = WhileStmt.make(null, null, 0, 0);
    vec = StmtVec.make(new Stmt[] {jmlStmt, javaWhileStmt});
    allStmts = BlockStmt.make(vec, 0, 0);
    fVisitor.visitBlockStmt(allStmts, fProp);
    evaluatedTerm = AnnotationDecoration.inst.getInvariant((ASTNode) javaWhileStmt);
    //***************Term**********************************
    expectedTerm = Logic.gt(xFieldAccessTermInt, sevenTermInt);
    //*************Test************************
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());
    
    
    //############# Expression ###########################
    // Set ghost = 0;
    // skip stmt;
    list.clear();
    binExpr = BinaryExpr.make(TagConstants.GT, xFieldAccessExprInt, zeroExprInt, loc2);
    jmlStmt = ExprStmtPragma.make(TagConstants.ASSERT, binExpr, null, loc2); 
    javaSkipStmt = SkipStmt.make(loc2); 
    vec = StmtVec.make(new Stmt[] {jmlStmt, javaSkipStmt});
    allStmts = BlockStmt.make(vec, 0, 0);
    fVisitor.visitBlockStmt(allStmts, fProp);
    list =  AnnotationDecoration.inst.getAnnotPre((ASTNode) javaSkipStmt);
    assumeTerm = list.get(0).formula;
    //***************Term**********************************
    expectedTerm = Logic.gt(xFieldAccessTermInt, zeroTermInt);
    //*************Test************************
    assertEquals(expectedTerm.toString(), assumeTerm.toString());  
    
    
    //  ############# Expression ###########################
    // ghost int ghosti;
    final SimpleModifierPragma modPragma = SimpleModifierPragma.make(TagConstants.GHOST, 0);
    final ModifierPragmaVec modVec = ModifierPragmaVec.make(new ModifierPragma[]{modPragma});
    final LocalVarDecl ghostDecl = LocalVarDecl.make(0, modVec, Identifier.intern("ghosti"), JavafePrimitiveType.make(TagConstants.INTTYPE, 0), 0, null, 0);
    VarDeclStmt ghostStmt = VarDeclStmt.make(ghostDecl);    
    javaSkipStmt = SkipStmt.make(loc2); 
    vec = StmtVec.make(new Stmt[] {ghostStmt, javaSkipStmt});
    allStmts = BlockStmt.make(vec, 0, 0);
    fVisitor.visitBlockStmt(allStmts, fProp);
    list =  AnnotationDecoration.inst.getAnnotPre((ASTNode) javaSkipStmt);
    Set ghostSet = (Set)list.get(0);
    Term evaluatedGhostDecl = ghostSet.declaration;
    //***************Term*********************************
    Term expectedGhostDecl = Expression.rvar(ghostDecl);
    //***************Test***********************************
    assertEquals(evaluatedGhostDecl.toString(), expectedGhostDecl.toString());

    
    //############# Expression ###########################
    // ghost int ghosti = 4;
    ghostDecl.init = LiteralExpr.make(TagConstants.INTLIT, 4, loc1);
    ghostStmt = VarDeclStmt.make(ghostDecl);
    vec = StmtVec.make(new Stmt[] {ghostStmt, javaSkipStmt});
    allStmts = BlockStmt.make(vec, 0, 0);
    fVisitor.visitBlockStmt(allStmts, fProp);
    list =  AnnotationDecoration.inst.getAnnotPre((ASTNode) javaSkipStmt);
    ghostSet = (Set)list.get(0);
    evaluatedGhostDecl = ghostSet.declaration;
    Term evaluatedGhostAssig = ghostSet.assignment.fExpr;
    //***************Term**********************************
    expectedGhostDecl = Expression.rvar(ghostDecl);
    Term expectedGhostAssig = Num.value((Integer) ((LiteralExpr) ghostDecl.init).value);
    //***************Test***********************************
    assertEquals(expectedGhostDecl.toString(), evaluatedGhostDecl.toString());
    assertEquals(expectedGhostAssig.toString(), evaluatedGhostAssig.toString());
    
    //############# Expression ###########################
    // set ghosti = 10;
    final LiteralExpr litExpr = LiteralExpr.make(TagConstants.INTLIT, 10, loc1);
    ghostDecl.init = LiteralExpr.make(TagConstants.INTLIT, 10, loc1);
    final VariableAccess ghostVar = VariableAccess.make(Identifier.intern("ghosti"), loc1, ghostDecl);
    final SetStmtPragma ghostSetStmt = SetStmtPragma.make(ghostVar, 0, litExpr, loc1);
    javaSkipStmt = SkipStmt.make(loc2); 
    vec = StmtVec.make(new Stmt[] {ghostSetStmt, javaSkipStmt});
    allStmts = BlockStmt.make(vec, 0, 0);
    fVisitor.visitBlockStmt(allStmts, fProp);
    list =  AnnotationDecoration.inst.getAnnotPre((ASTNode) javaSkipStmt);
    ghostSet = (Set)list.get(0);
    evaluatedGhostAssig = ghostSet.assignment.fExpr;
    expectedGhostAssig = Num.value((Integer) ((LiteralExpr) ghostDecl.init).value);
    //***************Test***********************************
    assertEquals(expectedGhostAssig.toString(), evaluatedGhostAssig.toString());
    
  }
  
  /**
   * Testing of exceptional postconditions, doesn't work yet....!!!
   */
  public void testVisitVarExprModifierPragma() {  
    //  signals_only  ArithmeticException;
    final LiteralExpr exprLeft = LiteralExpr.make(TagConstants.BOOLEANLIT, false, loc1);
    final VariableAccess varAccess = VariableAccess.make(Identifier.intern(""), loc2, null);
    final TypeName type = TypeName.make(SimpleName.make("ArithmeticException", loc1));
    final InstanceOfExpr exprRight = InstanceOfExpr.make(varAccess, type, loc1);
    final BinaryExpr exception = BinaryExpr.make(TagConstants.OR, exprLeft, exprRight, loc1);
   
    final javafe.ast.Type extype = (javafe.ast.Type) Types.javaLangException();
  /*  TypeSig test = (TypeSig)extype;   
    Object o3 = ((TypeSig)extype).getTypeDecl(); 
    Object test2 = Types.toClassTypeSig(extype);
    final Term typeOfException = Type.translate(extype);
   */
  //  FormalParaDecl args = FormalParaDecl.make(0, null, Identifier.intern(""), extype , loc1);
 //   final VarExprModifierPragma pragmaSignalsOnly = VarExprModifierPragma.make(TagConstants.SIGNALS, args, exception, loc1);
   // final ModifierPragmaVec pragmaVec = ModifierPragmaVec.make(new ModifierPragma[] {pragmaSignalsOnly});
   // final MethodDecl methodDecl = MethodDecl.make(0, pragmaVec, null, null, null, null, 0, 0, 0, 0, Identifier.intern("Test"), JavafePrimitiveType.make(103,0), 0);
  //  fProp.put("method", methodDecl);
    
    //***************Signals_only******************************
  //  Lookup.exceptionalPostconditions.put(methodDecl, new Post(Expression.rvar(Ref.sort), Logic.True())); 
  //  fVisitor.visitVarExprModifierPragma(pragmaSignalsOnly, fProp); //neue methode machen, da nicht in requires, ensures
  //  evaluatedTerm = ((Post) Lookup.exceptionalPostconditions.get(methodDecl)).getPost();
  }
  
  
  
  /**
   * Testing of Requires and Ensures features
   */
  public void testVisitExprModifierPragma() { 

    // requires x > 0;
    // ensures x > 0;
    
    binExpr = BinaryExpr.make(TagConstants.GT, xFieldAccessExprInt, zeroExprInt, loc2);
    ExprModifierPragma pragmaEnsures = ExprModifierPragma.make(TagConstants.ENSURES, binExpr, loc1);
    final ExprModifierPragma pragmaRequires = ExprModifierPragma.make(TagConstants.REQUIRES, binExpr, loc1);
    ModifierPragmaVec pragmaVec = ModifierPragmaVec.make(new ModifierPragma[] {pragmaEnsures, pragmaRequires});
    MethodDecl methodDecl = MethodDecl.make(0, pragmaVec, null, null, null, null, 0, 0, 0, 0, Identifier.intern("Test"), JavafePrimitiveType.make(103, 0), 0);
    fProp.put("method", methodDecl);
    
    //***************Requires******************************
    fVisitor.visitExprModifierPragma(pragmaRequires, fProp);
    evaluatedTerm = (Term) Lookup.preconditions.get(methodDecl);
    //***************Term**********************************
    expectedTerm = Logic.gt(xFieldAccessTermInt, zeroTermInt);
    //*************Test************************
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());
    
    //***************Ensures*******************************
    fVisitor.visitExprModifierPragma(pragmaEnsures, fProp);
    evaluatedTerm = ((Post) Lookup.postconditions.get(methodDecl)).getPost();
    //***************Term**********************************
    expectedTerm = Logic.gt(xFieldAccessTermInt, zeroTermInt);
    //*************Test************************
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());
    
    
    //  ensures \result > 0;
    ResExpr resultExpr = ResExpr.make(0);
    binExpr = BinaryExpr.make(TagConstants.GT, resultExpr, zeroExprInt, loc2);
    pragmaEnsures = ExprModifierPragma.make(TagConstants.ENSURES, binExpr, loc1);
    pragmaVec = ModifierPragmaVec.make(new ModifierPragma[] {pragmaEnsures});
    methodDecl = MethodDecl.make(0, pragmaVec, null, null, null, null, 0, 0, 0, 0, Identifier.intern("Test"), JavafePrimitiveType.make(103, 0), 0);
    fProp.put("method", methodDecl);
    fProp.put("result", Expression.getResultRVar(methodDecl));
    //**************Ensures*******************************
    fVisitor.visitExprModifierPragma(pragmaEnsures, fProp);
    evaluatedTerm = ((Post) Lookup.postconditions.get(methodDecl)).getPost();
    //***************Term**********************************
    expectedTerm = Logic.gt(Expression.rvar(Expression.getResultVar(methodDecl)), zeroTermInt);
    assertEquals(expectedTerm.toString(), evaluatedTerm.toString());
  }
  
  
  

  
  public void tearDown() {
    
  }

  
}

