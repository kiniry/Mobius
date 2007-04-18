package b2bpl.translation;

import java.util.ArrayList;
import java.util.List;

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
public final class CodeGenerator implements TranslationConstants {

  public static String quantVarName(String name) {
    return name;
  }

  public static BPLVariableExpression var(String name) {
    return new BPLVariableExpression(name);
  }

  public static BPLExpression fieldLoc(
      BPLExpression prefix,
      BPLExpression field) {
    return new BPLFunctionApplication(FIELD_LOC_FUNC, prefix, field);
  }

  public static BPLExpression fieldLoc(
      TranslationContext context,
      BPLExpression reference,
      BCField field) {
    if (field.isStatic()) {
      reference = typeObject(context.translateTypeReference(field.getOwner()));
    }
    return fieldLoc(reference, context.translateFieldReference(field));
  }

  public static BPLExpression arrayLoc(
      BPLExpression reference,
      BPLExpression index) {
    return new BPLFunctionApplication(ARRAY_LOC_FUNC, reference, index);
  }

  public static BPLExpression obj(BPLExpression location) {
    return new BPLFunctionApplication(OBJ_FUNC, location);
  }

  public static BPLExpression arrayLength(BPLExpression reference) {
    return new BPLFunctionApplication(ARRAY_LENGTH_FUNC, reference);
  }

  public static BPLExpression arrayType(BPLExpression type) {
    return new BPLFunctionApplication(ARRAY_TYPE_FUNC, type);
  }

  public static BPLExpression elementType(BPLExpression type) {
    return new BPLFunctionApplication(ELEMENT_TYPE_FUNC, type);
  }

  public static BPLExpression typeObject(BPLExpression type) {
    return new BPLFunctionApplication(TYPE_OBJECT_FUNC, type);
  }

  public static BPLExpression objectAlloc(BPLExpression type) {
    return new BPLFunctionApplication(OBJECT_ALLOC_FUNC, type);
  }

  public static BPLExpression arrayAlloc(
      BPLExpression type,
      BPLExpression length) {
    return new BPLFunctionApplication(ARRAY_ALLOC_FUNC, type, length);
  }

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

  public static BPLExpression multiArrayParent(BPLExpression value) {
    return new BPLFunctionApplication(MULTI_ARRAY_PARENT_FUNC, value);
  }

  public static BPLExpression multiArrayPosition(BPLExpression value) {
    return new BPLFunctionApplication(MULTI_ARRAY_POSITION_FUNC, value);
  }

  public static BPLExpression fieldType(BPLExpression field) {
    return new BPLFunctionApplication(FIELD_TYPE_FUNC, field);
  }

  public static BPLExpression isClassType(BPLExpression type) {
    return new BPLFunctionApplication(IS_CLASS_TYPE_FUNC, type);
  }

  public static BPLExpression isValueType(BPLExpression type) {
    return new BPLFunctionApplication(IS_VALUE_TYPE_FUNC, type);
  }
  
  public static BPLExpression isNormalReturnState(BPLExpression type) {
    return new BPLFunctionApplication(IS_NORMAL_RETURN_STATE_FUNC, type);
  }
  
  public static BPLExpression isExceptionalReturnState(BPLExpression type) {
    return new BPLFunctionApplication(IS_EXCEPTIONAL_RETURN_STATE_FUNC, type);
  }

  public static BPLExpression inv(
      BPLExpression type,
      BPLExpression object,
      BPLExpression heap) {
    return new BPLFunctionApplication(INV_FUNC, type, object, heap);
  }

  public static BPLExpression get(BPLExpression heap, BPLExpression variable) {
    return new BPLFunctionApplication(GET_FUNC, heap, variable);
  }

  public static BPLExpression update(
      BPLExpression heap,
      BPLExpression variable,
      BPLExpression value) {
    return new BPLFunctionApplication(UPDATE_FUNC, heap, variable, value);
  }

  public static BPLExpression alive(BPLExpression value, BPLExpression heap) {
    return new BPLFunctionApplication(ALIVE_FUNC, value, heap);
  }

  public static BPLExpression heapNew(
      BPLExpression heap,
      BPLExpression allocation) {
    return new BPLFunctionApplication(NEW_FUNC, heap, allocation);
  }

  public static BPLExpression heapNew(
      TranslationContext context,
      BPLExpression heap,
      JType type) {
    return heapNew(heap, objectAlloc(context.translateTypeReference(type)));
  }

  public static BPLExpression heapNewArray(
      TranslationContext context,
      BPLExpression heap,
      JType type,
      BPLExpression length) {
    return heapNew(
        heap,
        arrayAlloc(context.translateTypeReference(type), length));
  }

  public static BPLExpression heapAdd(
      BPLExpression heap,
      BPLExpression allocation) {
    return new BPLFunctionApplication(ADD_FUNC, heap, allocation);
  }

  public static BPLExpression heapAdd(
      TranslationContext context,
      BPLExpression heap,
      JType type) {
    return heapAdd(heap, objectAlloc(context.translateTypeReference(type)));
  }

  public static BPLExpression heapAddArray(
      TranslationContext context,
      BPLExpression heap,
      JType type,
      BPLExpression length) {
    return heapAdd(
        heap,
        arrayAlloc(context.translateTypeReference(type), length));
  }

  public static BPLExpression toint(BPLExpression value) {
    return new BPLFunctionApplication(TOINT_FUNC, value);
  }

  public static BPLExpression toref(BPLExpression value) {
    return new BPLFunctionApplication(TOREF_FUNC, value);
  }

  public static BPLExpression ival(BPLExpression integer) {
    return new BPLFunctionApplication(IVAL_FUNC, integer);
  }

  public static BPLExpression rval(BPLExpression reference) {
    return new BPLFunctionApplication(RVAL_FUNC, reference);
  }

  public static BPLExpression val(BPLExpression object, JType objectType) {
    if (type(objectType) == BPLBuiltInType.INT) {
      return new BPLFunctionApplication(IVAL_FUNC, object);
    }
    return new BPLFunctionApplication(RVAL_FUNC, object);
  }

  public static BPLExpression initVal(BPLExpression type) {
    return new BPLFunctionApplication(INIT_FUNC, type);
  }

  public static BPLExpression isStatic(BPLExpression value) {
    return new BPLFunctionApplication(STATIC_FUNC, value);
  }

  public static BPLExpression typ(BPLExpression value) {
    return new BPLFunctionApplication(TYP_FUNC, value);
  }

  public static BPLExpression ltyp(BPLExpression value) {
    return new BPLFunctionApplication(LTYP_FUNC, value);
  }

  public static BPLExpression allocType(BPLExpression allocation) {
    return new BPLFunctionApplication(ALLOC_TYPE_FUNC, allocation);
  }

  public static BPLExpression isOfType(
      BPLExpression object,
      BPLExpression type) {
    return new BPLFunctionApplication(IS_OF_TYPE_FUNC, object, type);
  }

  public static BPLExpression isInRange(
      BPLExpression integer,
      BPLExpression type) {
    return new BPLFunctionApplication(IS_IN_RANGE_FUNC, integer, type);
  }

  public static BPLExpression icast(
      BPLExpression expression,
      BPLExpression type) {
    return new BPLFunctionApplication(ICAST_FUNC, expression, type);
  }

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

  public static BPLExpression isInstanceOf(
      BPLExpression value,
      BPLExpression type) {
    return new BPLFunctionApplication(IS_INSTANCE_OF_FUNC, value, type);
  }

  public static BPLExpression bool2int(BPLExpression value) {
    return new BPLFunctionApplication(BOOL2INT_FUNC, value);
  }

  public static BPLExpression int2bool(BPLExpression value) {
    return new BPLFunctionApplication(INT2BOOL_FUNC, value);
  }

  public static BPLExpression bitShl(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(SHL_FUNC, left, right);
  }

  public static BPLExpression bitShr(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(SHR_FUNC, left, right);
  }

  public static BPLExpression bitUShr(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(USHR_FUNC, left, right);
  }

  public static BPLExpression bitAnd(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(AND_FUNC, left, right);
  }

  public static BPLExpression bitOr(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(OR_FUNC, left, right);
  }

  public static BPLExpression bitXor(
      BPLExpression left,
      BPLExpression right) {
    return new BPLFunctionApplication(XOR_FUNC, left, right);
  }
  
  public static BPLExpression fieldAccess(
      TranslationContext context,
      String heapVar,
      BPLExpression reference,
      BCField field) {
    BPLExpression val = get(var(heapVar), fieldLoc(context, reference, field));
    if (type(field.getType()) == BPLBuiltInType.INT) {
      return toint(val);
    }
    return toref(val);
  }

  public static BPLExpression fieldUpdate(
      TranslationContext context,
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

  public static BPLExpression nullLiteral() {
    return BPLNullLiteral.NULL;
  }

  public static BPLExpression add(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.PLUS,
        left,
        right);
  }

  public static BPLExpression sub(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.MINUS,
        left,
        right);
  }

  public static BPLExpression multiply(
      BPLExpression left,
      BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.TIMES,
        left,
        right);
  }

  public static BPLExpression divide(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.DIVIDE,
        left,
        right);
  }

  public static BPLExpression modulo(BPLExpression left, BPLExpression right) {
    return new BPLBinaryArithmeticExpression(
        BPLBinaryArithmeticExpression.Operator.REMAINDER,
        left,
        right);
  }

  public static BPLExpression neg(BPLExpression expr) {
    return new BPLUnaryMinusExpression(expr);
  }

  public static BPLExpression logicalNot(BPLExpression operand) {
    return new BPLLogicalNotExpression(operand);
  }

  public static BPLExpression logicalAnd(BPLExpression... operands) {
    // Filter all expressions that are not of type BPLBoolLiteral.TRUE 
    List<BPLExpression> ops = new ArrayList<BPLExpression>();
    for (BPLExpression expr : operands) {
      if (expr != BPLBoolLiteral.TRUE) {
        ops.add(expr);
      }
    }
    
    if (ops.size() == 0) {
      return BPLBoolLiteral.TRUE;
    }
    
    BPLExpression result = ops.get(0);
    for (int i = 1; i < ops.size(); i++) {
      result = new BPLBinaryLogicalExpression(
        BPLBinaryLogicalExpression.Operator.AND,
        result,
        ops.get(i));
    }
    return result;
  }

  public static BPLExpression logicalOr(BPLExpression... operands) {
    // Filter all expressions that are not of type BPLBoolLiteral.FALSE 
    List<BPLExpression> ops = new ArrayList<BPLExpression>();
    for (BPLExpression expr : operands) {
      if (expr != BPLBoolLiteral.FALSE) {
        ops.add(expr);
      }
    }
    
    if (ops.size() == 0) {
      return BPLBoolLiteral.FALSE;
    }
    
    BPLExpression result = ops.get(0);
    for (int i = 1; i < ops.size(); i++) {
      result = new BPLBinaryLogicalExpression(
        BPLBinaryLogicalExpression.Operator.OR,
        result,
        ops.get(i));
    }
    return result;
  }

  public static BPLExpression implies(
      BPLExpression left,
      BPLExpression right) {
    return new BPLBinaryLogicalExpression(
        BPLBinaryLogicalExpression.Operator.IMPLIES,
        left,
        right);
  }

  public static BPLExpression isEquiv(
      BPLExpression left,
      BPLExpression right) {
    return new BPLBinaryLogicalExpression(
        BPLBinaryLogicalExpression.Operator.EQUIVALENCE,
        left,
        right);
  }

  public static BPLExpression isEqual(BPLExpression left, BPLExpression right) {
    return new BPLEqualityExpression(
        BPLEqualityExpression.Operator.EQUALS,
        left,
        right);
  }

  public static BPLExpression notEqual(
      BPLExpression left,
      BPLExpression right) {
    return new BPLEqualityExpression(
        BPLEqualityExpression.Operator.NOT_EQUALS,
        left,
        right);
  }

  public static BPLExpression less(BPLExpression left, BPLExpression right) {
    return new BPLRelationalExpression(
        BPLRelationalExpression.Operator.LESS,
        left,
        right);
  }

  public static BPLExpression greater(BPLExpression left, BPLExpression right) {
    return new BPLRelationalExpression(
        BPLRelationalExpression.Operator.GREATER,
        left,
        right);
  }

  public static BPLExpression lessEqual(
      BPLExpression left,
      BPLExpression right) {
    return new BPLRelationalExpression(
        BPLRelationalExpression.Operator.LESS_EQUAL,
        left,
        right);
  }

  public static BPLExpression greaterEqual(
      BPLExpression left,
      BPLExpression right) {
    return new BPLRelationalExpression(
        BPLRelationalExpression.Operator.GREATER_EQUAL,
        left,
        right);
  }

  public static BPLExpression isSubtype(
      BPLExpression left,
      BPLExpression right) {
    return new BPLPartialOrderExpression(left, right);
  }

  public static BPLExpression nonNull(BPLExpression expression) {
    return new BPLEqualityExpression(
        BPLEqualityExpression.Operator.NOT_EQUALS,
        expression,
        BPLNullLiteral.NULL);
  }

  public static BPLExpression isNull(BPLExpression expression) {
    return new BPLEqualityExpression(
        BPLEqualityExpression.Operator.EQUALS,
        expression,
        BPLNullLiteral.NULL);
  }

  public static BPLExpression forall(
      BPLVariable variable,
      BPLExpression expression,
      BPLTrigger... triggers) {
    return forall(
        new BPLVariable[] { variable },
        expression,
        triggers);
  }

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

  public static BPLExpression exists(
      BPLVariable[] variables,
      BPLExpression expression) {
    return new BPLQuantifierExpression(
        BPLQuantifierExpression.Operator.EXISTS,
        variables,
        expression);
  }

  public static BPLTrigger trigger(BPLExpression... expressions) {
      return new BPLTrigger(expressions);
  }

  public static BPLCastExpression cast(
      BPLExpression expression,
      BPLType targetType) {
    return new BPLCastExpression(expression, targetType);
  }

  public static BPLBuiltInType type(JType type) {
    return type.isBaseType() ? BPLBuiltInType.INT : BPLBuiltInType.REF;
  }
}
