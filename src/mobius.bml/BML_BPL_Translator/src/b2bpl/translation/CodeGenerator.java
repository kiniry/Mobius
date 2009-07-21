package b2bpl.translation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import b2bpl.Main;
import b2bpl.bpl.ast.BPLBinaryArithmeticExpression;
import b2bpl.bpl.ast.BPLBinaryLogicalExpression;
import b2bpl.bpl.ast.BPLBoolLiteral;
import b2bpl.bpl.ast.BPLBuiltInType;
import b2bpl.bpl.ast.BPLCastExpression;
import b2bpl.bpl.ast.BPLEqualityExpression;
import b2bpl.bpl.ast.BPLExpression;
import b2bpl.bpl.ast.BPLFunctionApplication;
import b2bpl.bpl.ast.BPLLogicalNotExpression;
import b2bpl.bpl.ast.BPLNullLiteral;
import b2bpl.bpl.ast.BPLOldExpression;
import b2bpl.bpl.ast.BPLPartialOrderExpression;
import b2bpl.bpl.ast.BPLQuantifierExpression;
import b2bpl.bpl.ast.BPLRelationalExpression;
import b2bpl.bpl.ast.BPLTrigger;
import b2bpl.bpl.ast.BPLType;
import b2bpl.bpl.ast.BPLUnaryMinusExpression;
import b2bpl.bpl.ast.BPLVariable;
import b2bpl.bpl.ast.BPLVariableExpression;
import b2bpl.bytecode.BCField;
import b2bpl.bytecode.JArrayType;
import b2bpl.bytecode.JType;


/**
 * Simple utility class providing convenience methods to generate BoogiePL code
 * for frequently used expressions.
 *
 * <p>
 * In particular, this class provides the following flavors of static helper
 * methods:
 * <ul>
 *   <li>
 *     Simple wrapper methods for constructing the individual {@code BPLNode}s
 *     of the BoogiePL abstract syntax tree. These methods are mainly intended
 *     to provide a less verbose construction mechanism for a BoogiePL AST.
 *   </li>
 *   <li>
 *     Simple helper methods for generating combinations of
 *     {@code BPLExpression}s for frequently used patterns.
 *   </li>
 *   <li>
 *     Simple convenience methods representing the individual BoogiePL functions
 *     defined as part of the background predicate.
 *   </li>
 * </ul>
 * </p>
 *
 * @author Ovidio Mallo
 */
public final class CodeGenerator implements ITranslationConstants {

  //@ requires name != null;
  //@ ensures \result == name;
  public static String quantVarName(String name) {
    return name;
  }

  //@ requires name != null;
  //@ ensures \result != null;
  public static BPLVariableExpression var(String name) {
    return new BPLVariableExpression(name);
  }
  
  //@ requires var != null;
  //@ ensures \result != null;
  public static BPLOldExpression old(BPLVariableExpression var) {
    return new BPLOldExpression(var);
  }

  //@ requires prefix != null && field != null;
  //@ ensures \result != null;
  public static BPLExpression fieldLoc(
      BPLExpression prefix,
      BPLExpression field) {
    return new BPLFunctionApplication(FIELD_LOC_FUNC, prefix, field);
  }

  //@ requires context != null && reference != null && field != null;
  //@ ensures \result != null;
  public static BPLExpression fieldLoc(
      ITranslationContext context,
      BPLExpression reference,
      BCField field) {
    if (field.isStatic()) {
      reference = typeObject(context.translateTypeReference(field.getOwner()));
    }
    return fieldLoc(reference, context.translateFieldReference(field));
  }

  //@ requires reference != null && index != null;
  //@ ensures \result != null;
  public static BPLExpression arrayLoc(
      BPLExpression reference,
      BPLExpression index) {
    return new BPLFunctionApplication(ARRAY_LOC_FUNC, reference, index);
  }

  //@ requires location != null;
  //@ ensures \result != null;
  public static BPLExpression obj(BPLExpression location) {
    return new BPLFunctionApplication(OBJ_FUNC, location);
  }

  //@ requires reference != null;
  //@ ensures \result != null;
  public static BPLExpression arrayLength(BPLExpression reference) {
    return new BPLFunctionApplication(ARRAY_LENGTH_FUNC, reference);
  }

  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression arrayType(BPLExpression type) {
    return new BPLFunctionApplication(ARRAY_TYPE_FUNC, type);
  }

  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression elementType(BPLExpression type) {
    return new BPLFunctionApplication(ELEMENT_TYPE_FUNC, type);
  }

  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression typeObject(BPLExpression type) {
    return new BPLFunctionApplication(TYPE_OBJECT_FUNC, type);
  }

  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression objectAlloc(BPLExpression type) {
    return new BPLFunctionApplication(OBJECT_ALLOC_FUNC, type);
  }

  //@ requires type != null && length != null;
  //@ ensures \result != null;
  public static BPLExpression arrayAlloc(
      BPLExpression type,
      BPLExpression length) {
    return new BPLFunctionApplication(ARRAY_ALLOC_FUNC, type, length);
  }

  //@ requires type != null && length != null && allocation != null;
  //@ ensures \result != null;
  public static BPLExpression multiArrayAlloc(
      BPLExpression type,
      BPLExpression length,
      BPLExpression allocation) {
    return new BPLFunctionApplication(
        MULTI_ARRAY_ALLOC_FUNC,
        type,
        length,
        allocation);
  }

  //@ requires value != nul && heap != null && allocation != null;
  //@ ensures \result != null;
  public static BPLExpression isNewMultiArray(
      BPLExpression value,
      BPLExpression heap,
      BPLExpression allocation) {
    return new BPLFunctionApplication(
        IS_NEW_MULTI_ARRAY_FUNC,
        value,
        heap,
        allocation);
  }

  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression multiArrayParent(BPLExpression value) {
    return new BPLFunctionApplication(MULTI_ARRAY_PARENT_FUNC, value);
  }

  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression multiArrayPosition(BPLExpression value) {
    return new BPLFunctionApplication(MULTI_ARRAY_POSITION_FUNC, value);
  }

  //@ requires field != null;
  //@ ensures \result != null;
  public static BPLExpression fieldType(BPLExpression field) {
    return new BPLFunctionApplication(FIELD_TYPE_FUNC, field);
  }

  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression isClassType(BPLExpression type) {
    return new BPLFunctionApplication(IS_CLASS_TYPE_FUNC, type);
  }

  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression isValueType(BPLExpression type) {
    return new BPLFunctionApplication(IS_VALUE_TYPE_FUNC, type);
  }
  
  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression isNormalReturnState(BPLExpression type) {
    return new BPLFunctionApplication(IS_NORMAL_RETURN_STATE_FUNC, type);
  }
  
  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression isExceptionalReturnState(BPLExpression type) {
    return new BPLFunctionApplication(IS_EXCEPTIONAL_RETURN_STATE_FUNC, type);
  }

  //@ requires type != null && object != null && heap != null;
  //@ ensures \result != null;
  public static BPLExpression inv(
      BPLExpression type,
      BPLExpression object,
      BPLExpression heap) {
    return new BPLFunctionApplication(INV_FUNC, type, object, heap);
  }

  //@ requires heap != null && variable != null;
  //@ ensures \result != null;
  public static BPLExpression get(BPLExpression heap, BPLExpression variable) {
    return new BPLFunctionApplication(GET_FUNC, heap, variable);
  }

  //@ requires heap != null && variable != null && value != null;
  //@ ensures \result != null;
  public static BPLExpression update(
      BPLExpression heap,
      BPLExpression variable,
      BPLExpression value) {
    return new BPLFunctionApplication(UPDATE_FUNC, heap, variable, value);
  }

  //@ requires value != null && heap != null;
  //@ ensures \result != null;
  public static BPLExpression alive(BPLExpression value, BPLExpression heap) {
    return new BPLFunctionApplication(ALIVE_FUNC, value, heap);
  }

  //@ requires heap != null && allocation != null;
  //@ ensures \result != null;
  public static BPLExpression heapNew(
      BPLExpression heap,
      BPLExpression allocation) {
    return new BPLFunctionApplication(NEW_FUNC, heap, allocation);
  }

  //@ requires context != null && heap != null;
  //@ ensures \result != null;
  public static BPLExpression heapNew(
      ITranslationContext context,
      BPLExpression heap,
      JType type) {
    return heapNew(heap, objectAlloc(context.translateTypeReference(type)));
  }

  //@ requires context != null && heap != null;
  //@ ensures \result != null;
  public static BPLExpression heapNewArray(
      ITranslationContext context,
      BPLExpression heap,
      JType type,
      BPLExpression length) {
    return heapNew(
        heap,
        arrayAlloc(context.translateTypeReference(type), length));
  }

  //@ requires heap != null && allocation != null;
  //@ ensures \result != null;
  public static BPLExpression heapAdd(
      BPLExpression heap,
      BPLExpression allocation) {
    return new BPLFunctionApplication(ADD_FUNC, heap, allocation);
  }

  //@ requires context != null && heap != null;
  //@ ensures \result != null;
  public static BPLExpression heapAdd(
      ITranslationContext context,
      BPLExpression heap,
      JType type) {
    return heapAdd(heap, objectAlloc(context.translateTypeReference(type)));
  }

  //@ requires context != null && heap != null && type != null;
  //@ ensures \result != null;
  public static BPLExpression heapAddArray(
      ITranslationContext context,
      BPLExpression heap,
      JType type,
      BPLExpression length) {
    return heapAdd(heap, arrayAlloc(context.translateTypeReference(type), length));
  }
  
  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression toint(BPLExpression value) {
    return new BPLFunctionApplication(TOINT_FUNC, value);
  }

  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression toref(BPLExpression value) {
    return new BPLFunctionApplication(TOREF_FUNC, value);
  }

  //@ requires integer != null;
  //@ ensures \result != null;
  public static BPLExpression ival(BPLExpression integer) {
    return new BPLFunctionApplication(IVAL_FUNC, integer);
  }
  
  //@ requires reference != null;
  //@ ensures \result != null;
  public static BPLExpression rval(BPLExpression reference) {
    return new BPLFunctionApplication(RVAL_FUNC, reference);
  }

  //@ requires object != null && objectType != null;
  //@ ensures \result != null;
  public static BPLExpression val(BPLExpression object, JType objectType) {
    if (type(objectType) == BPLBuiltInType.INT) {
      return new BPLFunctionApplication(IVAL_FUNC, object);
    }
    return new BPLFunctionApplication(RVAL_FUNC, object);
  }

  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLExpression initVal(BPLExpression type) {
    return new BPLFunctionApplication(INIT_FUNC, type);
  }

  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression isStatic(BPLExpression value) {
    return new BPLFunctionApplication(STATIC_FUNC, value);
  }

  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression typ(BPLExpression value) {
    return new BPLFunctionApplication(TYP_FUNC, value);
  }

  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression ltyp(BPLExpression value) {
    return new BPLFunctionApplication(LTYP_FUNC, value);
  }

  //@ requires allocation != null;
  //@ ensures \result != null;
  public static BPLExpression allocType(BPLExpression allocation) {
    return new BPLFunctionApplication(ALLOC_TYPE_FUNC, allocation);
  }

  //@ requires object != null && type != null;
  //@ ensures \result != null;
  public static BPLExpression isOfType(
      BPLExpression object,
      BPLExpression type) {
    return new BPLFunctionApplication(IS_OF_TYPE_FUNC, object, type);
  }

  //@ requires integer != null && type != null;
  //@ ensures \result != null;
  public static BPLExpression isInRange(
      BPLExpression integer,
      BPLExpression type) {
    return new BPLFunctionApplication(IS_IN_RANGE_FUNC, integer, type);
  }

  //@ requires expression != null && type != null;
  //@ ensures \result != null;
  public static BPLExpression icast(
      BPLExpression expression,
      BPLExpression type) {
    return new BPLFunctionApplication(ICAST_FUNC, expression, type);
  }

  //@ requires condition != null && expression1 != null && expression2 != null;
  //@ ensures \result != null;
  public static BPLExpression ifThenElse(
      BPLExpression condition,
      BPLExpression expression1,
      BPLExpression expression2) {
    return new BPLFunctionApplication(
        IF_THEN_ELSE_FUNC,
        condition,
        expression1,
        expression2);
  }

  //@ requires value != null && type != null;
  //@ ensures \result != null;
  public static BPLExpression isInstanceOf(
      BPLExpression value,
      BPLExpression type) {
    return new BPLFunctionApplication(IS_INSTANCE_OF_FUNC, value, type);
  }

  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression bool2int(BPLExpression value) {
    return new BPLFunctionApplication(BOOL2INT_FUNC, value);
  }

  //@ requires value != null;
  //@ ensures \result != null;
  public static BPLExpression int2bool(BPLExpression value) {
    return new BPLFunctionApplication(INT2BOOL_FUNC, value);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression bitShl(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(SHL_FUNC, left, right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression bitShr(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(SHR_FUNC, left, right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression bitUShr(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(USHR_FUNC, left, right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression bitAnd(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(AND_FUNC, left, right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression bitOr(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(OR_FUNC, left, right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression bitXor(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(XOR_FUNC, left, right);
  }
  
  //@ requires context != null && heapVar != null && reference != null && field != null;
  //@ ensures \result != null;
  public static BPLExpression fieldAccess(
      ITranslationContext context,
      String heapVar,
      BPLExpression reference,
      BCField field) {
    BPLExpression val = get(var(heapVar), fieldLoc(context, reference, field));
    if (type(field.getType()) == BPLBuiltInType.INT) {
      return toint(val);
    }
    return toref(val);
  }

  //@ requires context != null && heapVar != null && reference != null && field != null && value != null;
  //@ ensures \result != null;
  public static BPLExpression fieldUpdate(
      ITranslationContext context,
      String heapVar,
      BPLExpression reference,
      BCField field,
      BPLExpression value) {
    BPLExpression loc = fieldLoc(context, reference, field);
    if (type(field.getType()) == BPLBuiltInType.INT) {
      return update(var(heapVar), loc, ival(value));
    }
    return update(var(heapVar), loc, rval(value));
  }

  //@ requires heapVar != null && arrayType != null && reference != null && index != null;
  //@ ensures \result != null;
  public static BPLExpression arrayAccess(
      String heapVar,
      JArrayType arrayType,
      BPLExpression reference,
      BPLExpression index) {
    BPLExpression val = get(var(heapVar), arrayLoc(reference, index));
    if (type(arrayType.getIndexedType()) == BPLBuiltInType.INT) {
      return toint(val);
    }
    return toref(val);
  }

  //@ requires heapVar != null && arrayType != null && reference != null && index != null && value != null;
  //@ ensures \result != null;
  public static BPLExpression arrayUpdate(
      String heapVar,
      JArrayType arrayType,
      BPLExpression reference,
      BPLExpression index,
      BPLExpression value) {
    BPLExpression loc = arrayLoc(reference, index);
    if (type(arrayType.getIndexedType()) == BPLBuiltInType.INT) {
      return update(var(heapVar), loc, ival(value));
    }
    return update(var(heapVar), loc, rval(value));
  }

  //@ ensures \result != null;
  public static BPLExpression nullLiteral() {
    return BPLNullLiteral.NULL;
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression add(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.PLUS,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression sub(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.MINUS,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression multiply(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.TIMES,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression divide(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.DIVIDE,
        left,
        right);
  }
  
  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression modulo(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.REMAINDER,
        left,
        right);
  }

  //@ requires expr != null;
  //@ ensures \result != null;
  public static BPLExpression neg(BPLExpression expr) {
    return new BPLUnaryMinusExpression(expr);
  }

  //@ requires operand != null;
  //@ ensures \result != null;
  public static BPLExpression logicalNot(BPLExpression operand) {
    return new BPLLogicalNotExpression(operand);
  }

  //@ requires operands != null;
  public static BPLExpression logicalAnd(BPLExpression... operands) {
    // Filter all expressions that are not of type BPLBoolLiteral.TRUE 
    List<BPLExpression> ops = new ArrayList<BPLExpression>();
    
    if (Main.getProject().simplifyLogicalExpressions()) {
      // Simplify logical expression (ignore "true" expressions)
      for (BPLExpression expr : operands) {
        if (expr != BPLBoolLiteral.TRUE) {
          ops.add(expr);
        }
        if (expr == BPLBoolLiteral.FALSE) return BPLBoolLiteral.FALSE;
      }
      
      if (ops.size() == 0) {
        return BPLBoolLiteral.TRUE;
      }
    } else {
      ops.addAll(Arrays.asList(operands));
    }
    
    if (ops.size() > 0) {
      BPLExpression result = ops.get(0);
      for (int i = 1; i < ops.size(); i++) {
        result = new BPLBinaryLogicalExpression(
          BPLBinaryLogicalExpression.Operator.AND,
          result,
          ops.get(i));
      }
      return result;
    }
    return null;
  }

  //@ requires operands != null;
  public static BPLExpression logicalOr(BPLExpression... operands) {
    // Filter all expressions that are not of type BPLBoolLiteral.FALSE 
    List<BPLExpression> ops = new ArrayList<BPLExpression>();
    
    if (Main.getProject().simplifyLogicalExpressions()) {
      for (BPLExpression expr : operands) {
        if (expr != BPLBoolLiteral.FALSE) {
          ops.add(expr);
        }
        if (expr == BPLBoolLiteral.TRUE) return BPLBoolLiteral.TRUE;
      }
      
      if (ops.size() == 0) {
        return BPLBoolLiteral.FALSE;
      }
    } else {
      ops.addAll(Arrays.asList(operands));
    }
    
    if (ops.size() > 0) {
      BPLExpression result = ops.get(0);
      for (int i = 1; i < ops.size(); i++) {
        result = new BPLBinaryLogicalExpression(
          BPLBinaryLogicalExpression.Operator.OR,
          result,
          ops.get(i));
      }
      return result;
    }
    return null;
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression implies(BPLExpression left, BPLExpression right) {
    
    // Simplify expression if flag it set
    if (Main.getProject().simplifyLogicalExpressions()) {
      if (left == BPLBoolLiteral.TRUE) {
        if (right == BPLBoolLiteral.TRUE) {
          return BPLBoolLiteral.TRUE;
        } else if (right == BPLBoolLiteral.FALSE) {
          return BPLBoolLiteral.FALSE;
        }
      } else if (left == BPLBoolLiteral.FALSE) {
         return BPLBoolLiteral.TRUE;
      } else {
        if (right == BPLBoolLiteral.TRUE) {
          return BPLBoolLiteral.TRUE;
        }
      }
    }
    
    return new BPLBinaryLogicalExpression(
        BPLBinaryLogicalExpression.Operator.IMPLIES,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression isEquiv(BPLExpression left, BPLExpression right) {
    return new BPLBinaryLogicalExpression(
        BPLBinaryLogicalExpression.Operator.EQUIVALENCE,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression isEqual(BPLExpression left, BPLExpression right) {
    return new BPLEqualityExpression(
        BPLEqualityExpression.Operator.EQUALS,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression notEqual(BPLExpression left, BPLExpression right) {
    return new BPLEqualityExpression(
        BPLEqualityExpression.Operator.NOT_EQUALS,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression less(BPLExpression left, BPLExpression right) {
    return new BPLRelationalExpression(
        BPLRelationalExpression.Operator.LESS,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression greater(BPLExpression left, BPLExpression right) {
    return new BPLRelationalExpression(
        BPLRelationalExpression.Operator.GREATER,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression lessEqual(BPLExpression left, BPLExpression right) {
    return new BPLRelationalExpression(
        BPLRelationalExpression.Operator.LESS_EQUAL,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression greaterEqual(BPLExpression left, BPLExpression right) {
    return new BPLRelationalExpression(
        BPLRelationalExpression.Operator.GREATER_EQUAL,
        left,
        right);
  }

  //@ requires left != null && right != null;
  //@ ensures \result != null;
  public static BPLExpression isSubtype(BPLExpression left, BPLExpression right) {
    return new BPLPartialOrderExpression(left, right);
  }

  //@ requires expression != null;
  //@ ensures \result != null;
  public static BPLExpression nonNull(BPLExpression expression) {
    return new BPLEqualityExpression(
        BPLEqualityExpression.Operator.NOT_EQUALS,
        expression,
        BPLNullLiteral.NULL);
  }

  //@ requires expression != null;
  //@ ensures \result != null;
  public static BPLExpression isNull(BPLExpression expression) {
    return new BPLEqualityExpression(
        BPLEqualityExpression.Operator.EQUALS,
        expression,
        BPLNullLiteral.NULL);
  }

  //@ requires variable != null && expression != null;
  //@ ensures \result != null;
  public static BPLExpression forall(
      BPLVariable variable,
      BPLExpression expression,
      BPLTrigger... triggers) {
    return forall(
        new BPLVariable[] { variable },
        expression,
        triggers);
  }

  //@ requires variable1 != null && variable2 != null && expression != null;
  //@ ensures \result != null;
  public static BPLExpression forall(
      BPLVariable variable1,
      BPLVariable variable2,
      BPLExpression expression,
      BPLTrigger... triggers) {
    return forall(
        new BPLVariable[] { variable1, variable2 },
        expression,
        triggers);
  }

  //@ requires variable1 != null && variable2 != null && variable3 != null && expression != null;
  //@ ensures \result != null;
  public static BPLExpression forall(
      BPLVariable variable1,
      BPLVariable variable2,
      BPLVariable variable3,
      BPLExpression expression,
      BPLTrigger... triggers) {
    return forall(
        new BPLVariable[] { variable1, variable2, variable3 },
        expression,
        triggers);
  }

  //@ requires variable1 != null && variable2 != null && variable3 != null && variable4 != null && expression != null;
  //@ ensures \result != null;
  public static BPLExpression forall(
      BPLVariable variable1,
      BPLVariable variable2,
      BPLVariable variable3,
      BPLVariable variable4,
      BPLExpression expression,
      BPLTrigger... triggers) {
    return forall(
        new BPLVariable[] { variable1, variable2, variable3, variable4 },
        expression,
        triggers);
  }

  //@ requires variable1 != null && variable2 != null && variable3 != null && variable4 != null && variable5 != null && expression != null;
  //@ ensures \result != null;
  public static BPLExpression forall(
      BPLVariable variable1,
      BPLVariable variable2,
      BPLVariable variable3,
      BPLVariable variable4,
      BPLVariable variable5,
      BPLExpression expression,
      BPLTrigger... triggers) {
    return forall(
        new BPLVariable[] {
            variable1, variable2, variable3, variable4, variable5
        },
        expression,
        triggers);
  }

  //@ requires variables != null && expression != null;
  //@ ensures \result != null;
  public static BPLExpression forall(
      BPLVariable[] variables,
      BPLExpression expression,
      BPLTrigger... triggers) {
    return new BPLQuantifierExpression(
        BPLQuantifierExpression.Operator.FORALL,
        variables,
        triggers,
        expression);
  }

  //@ requires variables != null && expression != null;
  //@ ensures \result != null;
  public static BPLExpression exists(
      BPLVariable[] variables,
      BPLExpression expression) {
    return new BPLQuantifierExpression(
        BPLQuantifierExpression.Operator.EXISTS,
        variables,
        expression);
  }

  //@ requires expressions != null;
  public static BPLTrigger trigger(BPLExpression... expressions) {
    if (Main.getProject().useTriggers()) {
      return new BPLTrigger(expressions);
    } else {
      return null;
    }
  }

  //@ requires expression != null && targetType != null;
  //@ ensures \result != null;
  public static BPLCastExpression cast(
      BPLExpression expression,
      BPLType targetType) {
    return new BPLCastExpression(expression, targetType);
  }

  //@ requires type != null;
  //@ ensures \result != null;
  public static BPLBuiltInType type(JType type) {
    return type.isBaseType() ? BPLBuiltInType.INT : BPLBuiltInType.REF;
  }
}
