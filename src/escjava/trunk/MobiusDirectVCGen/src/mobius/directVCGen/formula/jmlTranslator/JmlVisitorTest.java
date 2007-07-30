package mobius.directVCGen.formula.jmlTranslator;

import java.beans.FeatureDescriptor;
import java.util.HashSet;
import java.util.Properties;

import com.sun.org.apache.xerces.internal.impl.xs.util.XInt;

import javafe.ast.*;
import javafe.ast.Type;
import javafe.util.Location;
import javafe.util.Set;
import mobius.directVCGen.formula.*;

import mobius.directVCGen.formula.Expression;

import escjava.ast.NaryExpr;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.tc.TypeSig;

import junit.framework.TestCase;

public class JmlVisitorTest extends TestCase {
  
  JmlVisitor fVisitor;
  JmlExprToFormula ftranslator;
  Properties fProp = new Properties();
  String expectedString = "";
  boolean expectedBool = true;
  Term expectedTerm = null;
  LiteralExpr left = null;
  LiteralExpr right = null;
  FieldAccess xExprInt = null;
  FieldAccess yExprInt = null;
  TypeName typeTwo = null;
  FieldDecl xFieldDeclInt = null;
  FieldDecl yFieldDeclInt = null;
  ClassDecl twoClassDecl = null;
  ClassDecl oneClassDecl = null;
  
  ExprObjectDesignator xOdExpr = null;
  ExprObjectDesignator yOdExpr = null;
  
  
  BinaryExpr binExpr = null;
  BinaryExpr binExpr1 = null; //  10 == -50 + 100
  BinaryExpr binExpr2 = null;
  BinaryExpr binExpr3 = null;
  BinaryExpr binExpr4 = null;
  BinaryExpr binExpr5 = null;
  BinaryExpr binExpr6 = null;
  LiteralExpr sevenExprInt;
  LiteralExpr fourExprInt;
  LiteralExpr zeorExprInt;
  LiteralExpr sevenExprReal;
  LiteralExpr fourExprReal;
  LiteralExpr zeorExprReal;
  
  Term expTerm1;
  Term expTerm2;
  Term expTerm3;
  Term expTerm4;
  Term expTerm5;
  Term expTerm6;
  
  
  Term fourInt; // int 4;
  Term zeroInt; // int 0;
  Term negFourInt; // int -4;
  Term sevenInt; //int 7;
  Term fourReal; // real 4;
  Term zeroReal; // real 0;
  Term negFourReal; //real -4;
  Term sevenReal; //real 7;
  QuantVariableRef xTermVarInt; 
  QuantVariableRef xTermVarReal;
  QuantVariableRef yTermVarInt;
  QuantVariableRef yTermVarReal;
  Term xTermFieldInt;
  Term xTermFieldReal;
  Term yTermFieldInt;
  Term yTermFieldReal;
  
  int loc1 = 100;
  int loc2 = 102;

  public void setUp() throws Exception
  {
    fVisitor = new JmlVisitor();
    ftranslator = new JmlExprToFormula(fVisitor);
  
    fProp = new Properties();
    fProp.put("pred", Boolean.TRUE);
    fProp.put("old", Boolean.FALSE);
    fProp.put("visibleTypeSet", new HashSet<QuantVariableRef>());
    fProp.put("assignableSet", new HashSet<QuantVariableRef[]>());
    fProp.put("freshSet", new HashSet<Term>());
    fProp.put("nothing", Boolean.FALSE); //used for assignable
    fProp.put("interesting", Boolean.FALSE);
    fProp.put("firstPost", Boolean.TRUE);
    fProp.put("routinebegin", Boolean.TRUE);  
    fProp.put("quantifier", Boolean.FALSE);
    fProp.put("quantVars", new HashSet<QuantVariable>());
    fProp.put("isHelper", Boolean.FALSE);
    fProp.put("fresh", Boolean.FALSE);
    
    fourInt = Num.value((Integer) 4);
    zeroInt = Num.value((Integer) 0);
    negFourInt = Num.value((Integer) 4); // geht nicht für neg;
    sevenInt = Num.value((Integer) 7);
    fourReal = Num.value((Double) 4.0);
    zeroReal = Num.value((Double) 0.0);
    negFourReal = Num.value((Double) 4.0); //geht nicht für neg;
    sevenReal = Num.value((Double) 7.0);
    xTermVarInt = Expression.rvar("x", Num.sortInt);
    xTermVarReal = Expression.rvar("x", Num.sortReal);
    yTermVarInt = Expression.rvar("y", Num.sortInt);
    yTermVarReal = Expression.rvar("y", Num.sortReal);
    
   
//*********************** Decls *****************************************************    
    
    twoClassDecl = ClassDecl.make(0, null, Identifier.intern("Two"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
    oneClassDecl = ClassDecl.make(0, null, Identifier.intern("One"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
    xFieldDeclInt = FieldDecl.make(0, null, Identifier.intern("x"), JavafePrimitiveType.make(103, loc1), 0, null, 0);
    yFieldDeclInt = FieldDecl.make(0, null, Identifier.intern("y"), JavafePrimitiveType.make(103, loc1), 0, null, 0);
    xFieldDeclInt.parent = twoClassDecl;
    yFieldDeclInt.parent = twoClassDecl;
    
    
    xOdExpr = ExprObjectDesignator.make(loc2, ThisExpr.make(null, loc1));
    yOdExpr = ExprObjectDesignator.make(loc1, ThisExpr.make(null, loc2));
    
    
    
//*********************** Terms *****************************************************
    
    
    fourInt = Num.value((Integer) 4);
    zeroInt = Num.value((Integer) 0);
    negFourInt = Num.value((Integer) 4); // geht nicht für neg;
    sevenInt = Num.value((Integer) 7);
    fourReal = Num.value((Double) 4.0);
    zeroReal = Num.value((Double) 0.0);
    negFourReal = Num.value((Double) 4.0); //geht nicht für neg;
    sevenReal = Num.value((Double) 7.0);
    xTermVarInt = Expression.rvar("x", Num.sortInt);
    xTermVarReal = Expression.rvar("x", Num.sortReal);
    yTermVarInt = Expression.rvar("y", Num.sortInt);
    yTermVarReal = Expression.rvar("y", Num.sortReal);
    xTermFieldInt = Heap.select(Heap.var, Ref.varThis, Expression.var(xFieldDeclInt));
    yTermFieldInt = Heap.select(Heap.var, Ref.varThis, Expression.var(yFieldDeclInt));
    
    

    
//  *********************** Exprs *****************************************************    
    
    sevenExprInt = LiteralExpr.make(TagConstants.INTLIT, 7, loc1);
    fourExprInt = LiteralExpr.make(TagConstants.INTLIT, 4, loc2);
    zeorExprInt = LiteralExpr.make(TagConstants.INTLIT, 0, loc2);
    sevenExprReal = LiteralExpr.make(TagConstants.DOUBLELIT , 7, loc1);
    fourExprReal = LiteralExpr.make(TagConstants.DOUBLELIT, 4, loc2);
    zeorExprReal = LiteralExpr.make(TagConstants.DOUBLELIT, 0, loc2);
    
    xExprInt = FieldAccess.make(xOdExpr, Identifier.intern("x"), loc1);
    xExprInt.decl = xFieldDeclInt;
    yExprInt = FieldAccess.make(yOdExpr, Identifier.intern("x"), loc2);
    yExprInt.decl = yFieldDeclInt;
    
    
  }
  
  
  
  /**
   * Testing of JmlExprToFormula.eq(Expr, Object)
   *
   */
  public void testEq(){
    
    fProp.put("interesting", Boolean.TRUE); //fuer alle
    
    
    // 4 == ((7*0)+4)
    fProp.put("pred", Boolean.TRUE);
    expTerm1 = Logic.equals(fourInt, Num.add(Num.mul(sevenInt, zeroInt), fourInt));
    binExpr1 = javafe.ast.BinaryExpr.make(TagConstants.STAR, sevenExprInt, zeorExprInt, 0);
    binExpr1 = javafe.ast.BinaryExpr.make(TagConstants.ADD, binExpr1, fourExprInt,0);
    binExpr1 = javafe.ast.BinaryExpr.make(TagConstants.EQ, fourExprInt, binExpr1, 0);
    assertEquals(expTerm1.toString(), fVisitor.visitBinaryExpr(binExpr1, fProp).toString());
    
    // 4 == ((7*0)+4)
    fProp.put("pred", Boolean.FALSE);
    expTerm1 = Bool.equals(fourInt, Num.add(Num.mul(sevenInt, zeroInt), fourInt)); 
    assertEquals(expTerm1.toString(), fVisitor.visitBinaryExpr(binExpr1, fProp).toString());
    
    
    //  x == 4
    fProp.put("pred", Boolean.FALSE);
    binExpr2= javafe.ast.BinaryExpr.make(TagConstants.EQ, xExprInt, fourExprInt,  0); 
    expTerm2 = Bool.equals(xTermFieldInt, fourInt); 
    assertEquals(expTerm2.toString(), fVisitor.visitBinaryExpr(binExpr2, fProp).toString());
    
    
//  (x > 7 ) == (4 == y)
    fProp.put("pred", Boolean.FALSE);
    binExpr1 = javafe.ast.BinaryExpr.make(TagConstants.GT, xExprInt, sevenExprInt, loc1);
    binExpr2 = javafe.ast.BinaryExpr.make(TagConstants.EQ, fourExprInt, yExprInt, loc2);
    binExpr = javafe.ast.BinaryExpr.make(TagConstants.EQ, binExpr1, binExpr2, loc2);
    expTerm2 = Bool.equals(Bool.gt(xTermFieldInt, sevenInt), Bool.equals(fourInt, yTermFieldInt)); 
    String ow =  fVisitor.visitBinaryExpr(binExpr2, fProp).toString();
    String tw = expTerm2.toString();
    assertEquals(expTerm2.toString(), fVisitor.visitBinaryExpr(binExpr, fProp).toString());
    // the same with pred = true
    fProp.put("pred", Boolean.TRUE);
    expTerm2 = Logic.equals(Bool.gt(xTermFieldInt, sevenInt), Bool.equals(fourInt, yTermFieldInt)); 
    assertEquals(expTerm2.toString(), fVisitor.visitBinaryExpr(binExpr, fProp).toString());
    
//  ************FUNKT***********************************************************************************3
    
    
  }
  
  /**
   * Testing of \fresh JML feature in JmlExprToFormula.freshExpression(NaryExpr, Object)
   * 
   *
   */
  public void testfreshExpression() { 
    
    // \fresh (this.e, this.a) whereas this = Ego and e, a of type Ego
    fProp.put("interesting", Boolean.TRUE);
    
    
   /* ExprObjectDesignator eOd = ExprObjectDesignator.make(loc1, ThisExpr.make(null, loc1));
    ExprObjectDesignator aOd = ExprObjectDesignator.make(loc2, ThisExpr.make(null, loc2));
    TypeName ego = TypeName.make(Name.make("Ego", loc1));
    FieldDecl aDecl  = FieldDecl.make(0, null, Identifier.intern("a"), ego, 0, null, 0);
    FieldDecl eDecl = FieldDecl.make(0, null, Identifier.intern("e"), ego, 0, null, 0);
    FieldAccess eField = FieldAccess.make(eOd, Identifier.intern("e"), loc1);
    FieldAccess aField = FieldAccess.make(aOd, Identifier.intern("a"), loc2);
    ClassDecl parent = ClassDecl.make(0, null, Identifier.intern("Ego"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
    eDecl.parent = parent;
    aDecl.parent = parent;
    eField.decl = eDecl;
    aField.decl = aDecl;*/
    ExprVec veci = ExprVec.make(2);
    veci.addElement(xExprInt); //(eField);
    //veci.addElement(yExprInt); //(aField);
    NaryExpr nExpr = NaryExpr.make(0, 10, escjava.ast.TagConstants.FRESH, null, veci);
    QuantVariableRef test = Expression.rvar(xFieldDeclInt);
   /* expTerm1 = Logic.not(Logic.equalsNull(xTermFieldInt));
    expTerm2 = Logic.isAlive(Heap.var, xTermFieldInt);
    expTerm3 = Logic.not(Logic.isAlive(Heap.varPre, xTermFieldInt));
    expTerm4 = Logic.and(expTerm1, Logic.and(expTerm2, expTerm3));
    
    String exp = expTerm4.toString();
    String ge = ftranslator.freshExpression(nExpr, fProp).toString();
    
    //expectedString ="%and(%and(%and(%not(refEQ(?Ego?eFieldSignature:ref, null):PRED):PRED, %not(%isAlive(?\\pre_heap:map, ?Ego?eFieldSignature:ref):PRED):PRED):PRED, %isAlive(?heap:map, ?Ego?eFieldSignature:ref):PRED):PRED, %and(%and(%not(refEQ(?Ego?aFieldSignature:ref, null):PRED):PRED, %not(%isAlive(?\\pre_heap:map, ?Ego?aFieldSignature:ref):PRED):PRED):PRED, %isAlive(?heap:map, ?Ego?aFieldSignature:ref):PRED):PRED):PRED";
    NaryExpr nExpr2 = NaryExpr.make(0, 0, escjava.ast.TagConstants.FRESH, Identifier.intern("test"), veci);
   //assertEquals(expTerm4.toString(), ftranslator.freshExpression(nExpr, fProp).toString());
    */
    
    // \fresh (this.e, this.a) whereas this = Ego and e of type Ego and a of type Audi
   /* eOd = ExprObjectDesignator.make(loc1, ThisExpr.make(null, loc1));
    aOd = ExprObjectDesignator.make(loc2, ThisExpr.make(null, loc2));
    ego = TypeName.make(Name.make("Ego", loc1));
    final TypeName audi= TypeName.make(Name.make("Ego", loc1));
    aDecl  = FieldDecl.make(0, null, Identifier.intern("a"), audi, 0, null, 0);
    eDecl = FieldDecl.make(0, null, Identifier.intern("e"), ego, 0, null, 0);
    eField = FieldAccess.make(eOd, Identifier.intern("e"), loc1);
    aField = FieldAccess.make(aOd, Identifier.intern("a"), loc2);
    parent = ClassDecl.make(0, null, Identifier.intern("Ego"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
    eDecl.parent = parent;
    aDecl.parent = parent;
    eField.decl = eDecl;
    aField.decl = aDecl;
    veci = ExprVec.make(2);
    veci.addElement(eField);
    veci.addElement(aField);
    nExpr = NaryExpr.make(0, 10, escjava.ast.TagConstants.FRESH, null, veci);
    expectedString ="%and(%and(%and(%not(refEQ(?Ego?eFieldSignature:ref, null):PRED):PRED, %not(%isAlive(?\\pre_heap:map, ?Ego?eFieldSignature:ref):PRED):PRED):PRED, %isAlive(?heap:map, ?Ego?eFieldSignature:ref):PRED):PRED, %and(%and(%not(refEQ(?Ego?aFieldSignature:ref, null):PRED):PRED, %not(%isAlive(?\\pre_heap:map, ?Ego?aFieldSignature:ref):PRED):PRED):PRED, %isAlive(?heap:map, ?Ego?aFieldSignature:ref):PRED):PRED):PRED";
    assertEquals(expectedString, ftranslator.freshExpression(nExpr, fProp).toString());
    
    */
    
    
    
    
    
    
  
  }
  
  
  
  
  
  
  
  
  
  
  
  
  public void tearDown() {
    
  }

  
}





  




/**
 *    // QuantVariableRef qref = Expression.rvar(mobius.directVCGen.formula.Logic.sort);
   // LiteralExpr left = LiteralExpr.make(127, 20, 01);
   // LiteralExpr right = LiteralExpr.make(127, 30, 02);
   // javafe.ast.BinaryExpr binExpr = javafe.ast.BinaryExpr.make(420, left, right, 0);
   // testvisitBinaryExpr();
    * Identifier.intern("Name");
 */

////left = LiteralExpr.make(TagConstants.INTLIT, "x", loc1); 
//  ExprObjectDesignator xe = ExprObjectDesignator.make(0, ThisExpr.make(TypeSig.getRawSig(TypeName.make(Name.make("Two", loc1))), 0)); 
 // FieldAccess newleft = FieldAccess.make(xe,Identifier.intern("x"), 0);
  //FieldDecl newdecl = FieldDecl.make(0, null, Identifier.intern("x"), JavafePrimitiveType.make(103,0), 0, null, 0);
  //newleft.decl = newdecl;
  //newdecl.parent = ClassDecl.make(0, null, Identifier.intern("Two"), null, null, null, 0, 0, 0, 0, null);
  
 // final TypeName two= TypeName.make(Name.make("Two", loc1));
 // FieldDecl xxDecl  = FieldDecl.make(0, null, Identifier.intern("x"), two, 0, null, 0);
 // newleft.decl = xxDecl;
 // right = LiteralExpr.make(TagConstants.INTLIT, 7, loc1);
 /* Expr t1 = javafe.ast.BinaryExpr.make(TagConstants.GT, newleft, right, 0);
  left = LiteralExpr.make(TagConstants.INTLIT, 4, loc1);
  right = LiteralExpr.make(TagConstants.INTLIT, "y", loc1); 
  Expr t2 = javafe.ast.BinaryExpr.make(TagConstants.EQ, left, right, 0);
  binExpr2= javafe.ast.BinaryExpr.make(TagConstants.EQ, t1, t2,  0); 
  String test1 = expTerm2.toString();*/
//  String test2 = fVisitor.visitBinaryExpr(binExpr2, fProp).toString();
  
//  assertEquals(expTerm2.toString(), fVisitor.visitBinaryExpr(binExpr2, fProp).toString());
  
  
  
/*  ExprObjectDesignator xOd = ExprObjectDesignator.make(loc1, ThisExpr.make(null, loc1));
  TypeName ego = TypeName.make(Name.make("Two", loc1));
  FieldDecl xDecl  = FieldDecl.make(0, null, Identifier.intern("x"), ego, 0, null, 0);
  FieldAccess xField = FieldAccess.make(xOd, Identifier.intern("x"), loc1);
  ClassDecl parent = ClassDecl.make(0, null, Identifier.intern("Two"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
  xDecl.parent = parent;
  xField.decl = xDecl;
  ExprVec veci = ExprVec.make(2);
  veci.addElement(xField);
  FieldAccess xAccess = FieldAccess.make(xOd, Identifier.intern("x"),0); */
  
 // t1 = javafe.ast.BinaryExpr.make(TagConstants.GT, xAccess, right, 0);
 // binExpr2= javafe.ast.BinaryExpr.make(TagConstants.EQ, t1, t2,  0); 
 // String test2 = fVisitor.visitBinaryExpr(binExpr2, fProp).toString();
  
/* 
ClassDecl parentTwo = ClassDecl.make(0, null, Identifier.intern("Two"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
xFieldDecl = FieldDecl.make(0, null, Identifier.intern("x"), JavafePrimitiveType.make(103, loc1), 0, null, 0);
xFieldDecl.parent = parentTwo;
ExprObjectDesignator xOdExpr = ExprObjectDesignator.make(loc2, ThisExpr.make(null, loc1));

xExprInt = FieldAccess.make(xOdExpr, Identifier.intern("x"), loc1);
xExprInt.decl = xFieldDecl;

ExprObjectDesignator xOd = ExprObjectDesignator.make(loc1, ThisExpr.make(null, loc1));
typeTwo = TypeName.make(Name.make("Two", loc1));
FieldDecl xDecl  = FieldDecl.make(0, null, Identifier.intern("x"), typeTwo, 0, null, 0);
xIntField = FieldAccess.make(xOd, Identifier.intern("x"), loc1);
ClassDecl parent = ClassDecl.make(0, null, Identifier.intern("Two"), TypeNameVec.make(), null, TypeDeclElemVec.make(), loc1, loc2, loc1, loc2, null);
xDecl.parent = parentTwo;
xIntField.decl = xDecl;
ExprVec veci = ExprVec.make(2);
veci.addElement(xIntField);
FieldAccess xAccess = FieldAccess.make(xOd, Identifier.intern("x"),0);

*/
