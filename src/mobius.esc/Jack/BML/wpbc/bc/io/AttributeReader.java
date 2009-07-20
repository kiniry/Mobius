/*
 * Created on Jul 8, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bc.io;

import java.util.Vector;

import modifexpression.AllArrayElem;
import modifexpression.ArrayElemFromTo;
import modifexpression.Everything;
import modifexpression.ModifiesArray;
import modifexpression.ModifiesDOT;
import modifexpression.ModifiesExpression;
import modifexpression.ModifiesIdent;
import modifexpression.ModifiesLocalVariable;
import modifexpression.Nothing;
import modifexpression.SingleIndex;
import modifexpression.SpecArray;

import org.apache.bcel.classfile.Unknown;

import bcclass.BCConstantPool;
import bcclass.attributes.Assert;
import bcclass.attributes.AssertTable;
import bcclass.attributes.BCAttribute;
import bcclass.attributes.BCLineNumber;
import bcclass.attributes.BlockSpecification;
import bcclass.attributes.ClassInvariant;
import bcclass.attributes.Exsures;
import bcclass.attributes.ExsuresTable;
import bcclass.attributes.HistoryConstraints;
import bcclass.attributes.LoopSpecification;
import bcclass.attributes.MethodSpecification;
import bcclass.attributes.ModifiesSet;
import bcclass.attributes.SingleBlockSpecification;
import bcclass.attributes.SingleLoopSpecification;
import bcclass.attributes.SpecificationCase;
import bcexpression.ArithmeticExpression;
import bcexpression.ArrayAccessExpression;
import bcexpression.BCLocalVariable;
import bcexpression.BitExpression;
import bcexpression.CastExpression;
import bcexpression.CharLiteral;
import bcexpression.ConditionalExpression;
import bcexpression.Expression;
import bcexpression.ExpressionConstants;
import bcexpression.FieldAccess;
import bcexpression.NULL;
import bcexpression.NumberLiteral;
import bcexpression.Variable;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
import bcexpression.jml.ELEMTYPE;
import bcexpression.jml.JML_CONST_TYPE;
import bcexpression.jml.OLD;
import bcexpression.jml.RESULT;
import bcexpression.jml.TYPEOF;
import bcexpression.jml._TYPE;
import bcexpression.vm.Counter;
import bcexpression.vm.Stack;
import constants.ArrayLengthConstant;
import constants.BCConstant;
import constants.BCConstantFieldRef;
import constants.BCConstantMethodRef;
import constants.BCConstantUtf8;
import formula.Connector;
import formula.Formula;
import formula.Quantificator;
import formula.atomic.Predicate;
import formula.atomic.Predicate0Ar;
import formula.atomic.Predicate2Ar;
import formula.atomic.PredicateSymbol;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class AttributeReader {
	private static int pos;
	private static BCConstantPool constantPool;
	private static BCLineNumber[] lineNumberTable;
	private static BCLocalVariable[] localVariables;
	
	public static BCAttribute readAttribute(
		Unknown privateAttr,
		BCConstantPool _constantPool,
		BCLineNumber[] _lineNumberTable,
		BCLocalVariable[] _localVariables)
		throws ReadAttributeException {
		constantPool = _constantPool;
		lineNumberTable = _lineNumberTable; 
		localVariables = _localVariables;
		String name = privateAttr.getName();
		if (name.equals(BCAttribute.ASSERT)) {
			return readAssertTable(privateAttr.getBytes());
		}

		if (name.equals(BCAttribute.MethodSpecification)) {
			return readMethodSpecification(privateAttr.getBytes());
		}

		if (name.equals(BCAttribute.LOOPSPECIFICATION)) {
			return readLoopSpecification(privateAttr.getBytes());
		}
		if (name.equals(BCAttribute.BLOCKSPECIFICATION)) {
			return readBlockSpecification(privateAttr.getBytes());
		}
		if (name.equals(BCAttribute.HISTORY_CONSTRAINTS)) {
			return readHistoryConstraints(privateAttr.getBytes());
		}
		if (name.equals(BCAttribute.CLASSINVARIANT)) {
			return readClassInvariant(privateAttr.getBytes());
		}
		return null;
	}

	///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//////////////////////////////////////Class Specification/////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	private static HistoryConstraints readHistoryConstraints(byte[] bytes)
		throws ReadAttributeException {
		//here the length of the attribute not needed
		pos = 0;
		Formula predicate = readFormula(bytes);
		HistoryConstraints historyConstraints =
			new HistoryConstraints(predicate);
		return historyConstraints;
	}

	private static ClassInvariant readClassInvariant(byte[] bytes)
		throws ReadAttributeException {
		//		here the length of the attribute not needed
		pos = 0;
		Formula predicate = readFormula(bytes);
		ClassInvariant classInvariant = new ClassInvariant(predicate);
		return classInvariant;
	}

	//////////////////////////////////////////end Class specification//////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//////////////////////////////////////Method Specification/////////////////////////////////////////////
	//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	////////////////////// start : block specification /////////////////////////////////////////////////
	private static BlockSpecification readBlockSpecification(byte[] bytes)
		throws ReadAttributeException {
		pos = 0;
		int attribute_length = bytes.length;
		int attributes_count = readAttributeCount(bytes);
		if (attribute_length == 2) {
			return null;
		}
		if (attributes_count <= 0) {
			throw new ReadAttributeException(
				"a wrong BlockSpecification attribute : attribute count  = "
					+ attributes_count
					+ " and attribute length =  "
					+ attribute_length);
		}
		SingleBlockSpecification[] blockSpecs =
			new SingleBlockSpecification[attributes_count];
		for (int i = 0; i < attributes_count; i++) {
			blockSpecs[i] = readSingleBlockSpecification(bytes);
		}
		BlockSpecification blockSpec = new BlockSpecification(blockSpecs);
		return blockSpec;
	}

	/**
	 * @param bytes
	 * @return
	 */
	private static SingleBlockSpecification readSingleBlockSpecification(byte[] bytes)
		throws ReadAttributeException {
		int startCpInd = readShort(bytes);
		int endCpInd = readShort(bytes);
		Formula precondition = readFormula(bytes);
		int modifiesCount = readShort(bytes);
		Expression[] modifies = null;
		if (modifiesCount > 0) {
			modifies = new Expression[modifiesCount];
			for (int i = 0; i < modifiesCount; i++) {
				modifies[i] = readExpression(bytes);
			}
		}
		Formula postcondition = readFormula(bytes);
		SingleBlockSpecification blockSpec =
			new SingleBlockSpecification(
				startCpInd,
				endCpInd,
				precondition,
				modifies,
				postcondition);
		return blockSpec;
	}

	////////////////////// end : block specification /////////////////////////////////////////////////

	////////////////////// start : loopspecifcation /////////////////////////////////////////////////

	private static LoopSpecification readLoopSpecification(byte[] bytes)
		throws ReadAttributeException {
	
		pos = 0;
		int attribute_length = bytes.length;
		int attributes_count = readAttributeCount(bytes);
		if (attribute_length == 2) {
			return null;
		}
		if (attributes_count <= 0) {
			throw new ReadAttributeException(
				"a wrong LoopSpecification attribute : attribute count  = "
					+ attributes_count
					+ " and attribute length  = "
					+ attribute_length);
		}
		SingleLoopSpecification[] loopSpecs =
			new SingleLoopSpecification[attributes_count];
		for (int i = 0; i < attributes_count; i++) {
			if (pos >= attribute_length) {
				throw new ReadAttributeException(
					"uncorrect LoopSpecification  attribute attribute_length "
						+ attribute_length
						+ " <  actual length of attribute ");
			}
			loopSpecs[i] = readSingleLoopSpecification(bytes);
//			Util.dump(" readSingleLoopSpecification  pos = " +pos) ;
		}
		LoopSpecification loopSpe = new LoopSpecification(loopSpecs);
		return loopSpe;
	}

	private static SingleLoopSpecification readSingleLoopSpecification(byte[] bytes)
		throws ReadAttributeException {
		
		int lineNumber = readShort(bytes);
//		int loopStartPcInd  = lineNumberTable.getLineNumberTable()[ lineNumber].getStartPC();
		int loopStartPcInd  = lineNumberTable[ lineNumber].getStartPC();
//		Util.dump(" loopStartPC  pos = " +pos) ;
//		int modifiesCount = readShort(bytes);
		ModifiesSet modifies = readModifies(bytes);
//		Util.dump("readModifies pos = " + pos );
		Formula invariant = readFormula(bytes);
		Expression decreases = readExpression(bytes);
		SingleLoopSpecification loopSpec =
			new SingleLoopSpecification(
				loopStartPcInd,
				modifies,
				invariant,
				decreases);
		return loopSpec;
	}

	////////////////////// end : loopspecifcation /////////////////////////////////////////////////

	////////////////////// start : assert table /////////////////////////////////////////////////
	private static AssertTable readAssertTable(byte[] bytes)
		throws ReadAttributeException {
		pos = 0;
		int attribute_length = bytes.length;
		int attributes_count = readAttributeCount(bytes);
		if (attribute_length <= 0) {
			return null;
		}
		if (attributes_count == 0) {
			return null;
		}
		Assert[] asserts = new Assert[attributes_count];
		for (int i = 0; i < attributes_count; i++) {
			if (pos >= attribute_length) {
				throw new ReadAttributeException(
					"uncorrect Assert  attribute attribute_length "
						+ attribute_length
						+ " <  actual length of attribute ");
			}
			asserts[i] = readAssert(bytes);
		}
		AssertTable assertTable = new AssertTable(asserts);
		return assertTable;
	}

	/**
	 * @param pos - the position from which starts the assert object
	 * @param bytes -the array from which the assert object is read
	 * @param assert  - an object that should be initialised by the  method
	 * @return the leftmost index into the byte array bytes that is not read by the method
	 */
	private static Assert readAssert(byte[] bytes)
		throws ReadAttributeException {
		int pcIndex = readShort(bytes);
		Formula formula = readFormula(bytes);
		return new Assert(formula, pcIndex);
	}
	//////////////////////  end : assert table /////////////////////////////////////////////////

	//////////////////  start : method specification  /////////////////////////////////////////////////

	private static MethodSpecification readMethodSpecification(byte[] bytes)
		throws ReadAttributeException {
		pos = 0;
		int attribute_length = bytes.length;
		Formula precondition = readFormula(bytes);
		int attributes_count = readAttributeCount(bytes);
		if (attribute_length <= 0) {
			return null;
		}
		if (attributes_count <= 0) {
			throw new ReadAttributeException(
				"a wrong MethodSpecification  attribute : attribute count  = "
					+ attributes_count
					+ " and attribute length  =  "
					+ attribute_length
					+ "  ");
		}
		SpecificationCase[] specCases = new SpecificationCase[attributes_count];
		for (int i = 0; i < attributes_count; i++) {
			if ((pos - 6) >= attribute_length) {
				throw new ReadAttributeException(
					"uncorrect MethodSpec  attribute attribute_length "
						+ attribute_length
						+ " <  actual length of attribute ");
			}
			specCases[i] = readSpecificationCase(bytes);
		}
		MethodSpecification methodSpec =
			new MethodSpecification(precondition, specCases);
		return methodSpec;
	}

	private static SpecificationCase readSpecificationCase(byte[] bytes)
		throws ReadAttributeException {
		Formula precondition = readFormula(bytes);
		ModifiesSet modifies = readModifies(bytes);

		Formula postcondition = readFormula(bytes);
		ExsuresTable exsures = readExsuresTable(bytes);
		SpecificationCase specCase =
			new SpecificationCase(
				precondition,
				postcondition,
				modifies,
				exsures);
		return specCase;
	}

	/**
	 * @param bytes
	 * @return
	 */
	private static ModifiesSet readModifies(byte[] bytes)
		throws ReadAttributeException {

//		Util.dump("readModifies pos = " + pos );
		int modifiesCount = readAttributeCount(bytes);
//		Util.dump("modifies count  = " + modifiesCount );
//		Util.dump("readAttributeCount pos = " + pos );
		ModifiesExpression[] modifies = null;
		int _byte;
		if (modifiesCount > 0) {
			modifies = new ModifiesExpression[modifiesCount];
			for (int i = 0; i < modifiesCount; i++) {	
				modifies[i] = readModifiesExpression(bytes);
			}
		}
		if ( modifies == null) {
			ModifiesSet modifSet = new ModifiesSet(new ModifiesExpression[]{Everything.EVERYTHING}, constantPool);
			return modifSet;
		}
		ModifiesSet modifSet = new ModifiesSet(modifies, constantPool );
		return modifSet;
	}
	
	private static ModifiesExpression readModifiesExpression(byte[] bytes) throws ReadAttributeException {
		int _byte = readByte(bytes);
		if (_byte == Code.MODIFIES_NOTHING) {
			return Nothing.NOTHING;
		}
		if (_byte == Code.MODIFIES_EVERYTHING) {
			return Everything.EVERYTHING;
		}
		if (_byte == Code.MODIFIES_IDENT) {
			Expression  e = readExpression(bytes);
			if (e instanceof BCLocalVariable) {
				ModifiesLocalVariable modifLocVar = new ModifiesLocalVariable((BCLocalVariable)e, constantPool);
				return modifLocVar;
			}
			ModifiesIdent modifId = new ModifiesIdent(e, constantPool);
			return modifId;
		}
		if (_byte == Code.MODIFIES_DOT) {
			ModifiesExpression  ident = readModifiesExpression(bytes);
			Expression expr = readExpression(bytes);
			ModifiesDOT modifDot =  new ModifiesDOT( ident, expr, constantPool);
			return modifDot;
		}
		if (_byte == Code.MODIFIES_ARRAY ) {
			ModifiesExpression arrExpr = readModifiesExpression(bytes);
			SpecArray specArray = readSpecArray(bytes);
			ModifiesArray modArray = new ModifiesArray( arrExpr, specArray, constantPool);
			return modArray;
		}		
		return null;
	}

	private static SpecArray readSpecArray(byte[] bytes) throws ReadAttributeException {
		int _byte = readByte(bytes);
		
		if (_byte == Code.MODIFIES_SINGLE_INDICE) {
			Expression singleIndice = readExpression(bytes);
			SingleIndex index = new SingleIndex(singleIndice); 
			return index;
		}
		if (_byte == Code.MODIFIES_INTERVAL) {
			Expression start = readExpression(bytes);
			Expression end = readExpression(bytes);
			ArrayElemFromTo interval = new ArrayElemFromTo(start,end);
			return interval;
		} 
		if (_byte == Code.MODIFIES_STAR) {
			return AllArrayElem.ALLARRAYELEM;
		}	
		return null;
	}
	
	/**
	 * reads an exsures table
	 * @param bytes
	 * @return
	 */
	private static ExsuresTable readExsuresTable(byte[] bytes)
		throws ReadAttributeException {
		int exsuresCount = readAttributeCount(bytes);
		if (exsuresCount <= 0) {
			return null;
		}
		Exsures[] exsures = new Exsures[exsuresCount];
		for (int i = 0; i < exsuresCount; i++) {
			exsures[i] = readExsures(bytes);
		}
		ExsuresTable exsuresTable = new ExsuresTable(exsures);
		return exsuresTable;
	}

	private static Exsures readExsures(byte[] bytes)
		throws ReadAttributeException {
		JavaObjectType excType = (JavaObjectType) readJavaType(bytes);
		Formula exsFormula = readFormula(bytes);
		Exsures exsures = new Exsures(exsFormula, excType);
		return exsures;
	}
	////////////////////  end : method specification  /////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	//////////////////////////////////Attribute ///////////////////////////////////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////
	private static int readAttributeLength(byte[] bytes) {
		int attribute_length = readInt(bytes);
		return attribute_length;
	}

	private static int readAttributeCount(byte[] bytes) {
		int attribute_count = readShort(bytes);
		return attribute_count;
	}

	private static int readInt(byte[] bytes) {
		int integer =
			((bytes[pos] & 0xff) << 24)
				| ((bytes[pos + 1] & 0xff) << 16)
				| ((bytes[pos + 2] & 0xff) << 8)
				| (bytes[pos + 3] & 0xff);
		pos = pos + 4;
		return integer;
	}

	private static int readShort(byte[] bytes) {
		int _short = ((bytes[pos] & 0xff) << 8) | (bytes[pos + 1] & 0xff);
		pos = pos + 2;
		return _short;
	}

	private static char readChar(byte[] bytes) {
		char _char = (char) ((bytes[pos] << 8) | (bytes[pos + 1] & 0xff));
		pos = pos + 2;
		return _char;
	}

	private static int readByte(byte[] bytes) {
//		Util.dump("pos = " + pos );
		int _byte = bytes[pos] & 0xff;
		pos = pos + 1;
		return _byte;
	}
	
	/**
	 * this method serves to get the value in the next at position pos 
	 */
	private static int checkByteValue(byte[] bytes, int p) {
		int _byte = bytes[p] & 0xff;
		return _byte;
	}

	private static Formula readFormula(byte[] bytes)
		throws ReadAttributeException {
		int _byte = readByte(bytes);
		if (_byte == Code.TRUE) {
			return Predicate0Ar.TRUE;
		}
		if (_byte == Code.FALSE) {
			return Predicate0Ar.FALSE;
		}
		if (_byte == Code.AND) {
			Formula f1 = readFormula(bytes);
			Formula f2 = readFormula(bytes);
			Formula formula = Formula.getFormula(f1, f2, Connector.AND);
			return formula;
		}
		if (_byte == Code.OR) {
			Formula f1 = readFormula(bytes);
			Formula f2 = readFormula(bytes);
			Formula formula = Formula.getFormula(f1, f2, Connector.OR);
			return formula;
		}
		if (_byte == Code.IMPLIES) {
			Formula f1 = readFormula(bytes);
			Formula f2 = readFormula(bytes);
			Formula formula = Formula.getFormula(f1, f2, Connector.IMPLIES);
			return formula;
		}
		if (_byte == Code.NOT) {
			Formula f1 = readFormula(bytes);
			Formula formula = Formula.getFormula(f1, Connector.NOT);
			return formula;
		}
		if (_byte == Code.GRT) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate =
				Predicate2Ar.getPredicate(expr1, expr2, PredicateSymbol.GRT);
			return predicate;
		}
		if (_byte == Code.GRTEQ) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate =
				Predicate2Ar.getPredicate(expr1, expr2, PredicateSymbol.GRTEQ);
			return predicate;
		}
		if (_byte == Code.LESS) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate =
				Predicate2Ar.getPredicate(expr1, expr2, PredicateSymbol.LESS);
			return predicate;
		}
		if (_byte == Code.LESSEQ) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate =
				Predicate2Ar.getPredicate(expr1, expr2, PredicateSymbol.LESSEQ);
			return predicate;
		}
		if (_byte == Code.EQ) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate =
				Predicate2Ar.getPredicate(expr1, expr2, PredicateSymbol.EQ);
			return predicate;
		}
		if (_byte == Code.NOTEQ) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate =
				Formula.getFormula( Predicate2Ar.getPredicate(expr1, expr2, PredicateSymbol.EQ) , Connector.NOT);
			return predicate;
		}
		if (_byte == Code.INSTANCEOF) {
			Expression expr1 = readExpression(bytes);
			JavaType type = readJavaType(bytes);
			Formula predicate =
				new Predicate2Ar(type, expr1, PredicateSymbol.INSTANCEOF);
			return predicate;
		}
		if (_byte == Code.SUBTYPE) {
			JavaType type1 = readJavaType(bytes);
			JavaType type2 = readJavaType(bytes);
			Formula predicate =
				new Predicate2Ar(type1, type2, PredicateSymbol.SUBTYPE);
			return predicate;
		}
		if (_byte == Code.EXISTS) {

			
		}
		if (_byte == Code.FORALL) {
			int numBoundVars  = readByte(bytes);
			Variable[] vars = new Variable[numBoundVars ];
			for (int i = 0; i < numBoundVars ; i++) {
				JavaType jType = readJavaType(bytes);
				Variable var = new Variable(i, jType);
				vars[i] = var;
			}
			Quantificator forall= new Quantificator(Quantificator.FORALL, vars ); 
            Formula f = readFormula(bytes);
            Formula forallFormula = Formula.getFormula( f, forall);
            return forallFormula;
		}
		return null;
	}

	

	
    private static Expression readExpression(byte[] bytes)
		throws ReadAttributeException {
		int _byte = readByte(bytes);
		if (_byte == Code.PLUS) { // ARithmetic 
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				ArithmeticExpression.getArithmeticExpression(
					e1,
					e2,
					ExpressionConstants.ADD);
			return e;
		} else if (_byte == Code.MINUS) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				ArithmeticExpression.getArithmeticExpression(
					e1,
					e2,
					ExpressionConstants.SUB);
			return e;
		} else if (_byte == Code.MULT) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				ArithmeticExpression.getArithmeticExpression(
					e1,
					e2,
					ExpressionConstants.MULT);
			return e;
		} else if (_byte == Code.DIV) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				ArithmeticExpression.getArithmeticExpression(
					e1,
					e2,
					ExpressionConstants.DIV);
			return e;
		} else if (_byte == Code.REM) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				ArithmeticExpression.getArithmeticExpression(
					e1,
					e2,
					ExpressionConstants.REM);
			return e;
		} else if (_byte == Code.NEG) {
			Expression e1 = readExpression(bytes);
			Expression e =
				ArithmeticExpression.getArithmeticExpression(
					e1,
					ExpressionConstants.REM);
			return e;
		} else if (_byte == Code.BITWISEAND) { // Bitwise
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				new BitExpression(e1, e2, ExpressionConstants.BITWISEAND);
			return e;
		} else if (_byte == Code.BITWISEOR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				new BitExpression(e1, e2, ExpressionConstants.BITWISEOR);
			return e;
		} else if (_byte == Code.BITWISEXOR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				new BitExpression(e1, e2, ExpressionConstants.BITWISEXOR);
			return e;
		} else if (_byte == Code.SHL) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				// e1 the expression that is shifted 
		// e2 is  the number of  positions e1 to shift with 
	new BitExpression(e1, e2, ExpressionConstants.SHL);
			return e;
		} else if (_byte == Code.SHR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				// e1 the expression that is shifted 
		// e2 is  the number of  positions e1 to shift with 
	new BitExpression(e1, e2, ExpressionConstants.SHR);
			return e;
		} else if (_byte == Code.USHR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
				// e1 the expression that is shifted 
		// e2 is  the number of  positions e1 to shift with 
	new BitExpression(e1, e2, ExpressionConstants.USHR);
			return e;
		} else if (_byte == Code.INT_LITERAL) { // Literals
			int literal = readInt(bytes);
			Expression e = new NumberLiteral(literal);
			return e;
		} else if (_byte == Code.CHAR_LITERAL) {
			char literal = readChar(bytes);

			Expression e = new CharLiteral(literal);
			return e;
		} else if (_byte == Code.TYPE_OF) { // JML expressions 
			Expression e1 = readExpression(bytes);
			Expression e = new TYPEOF(e1);
			return e;
		} else if (_byte == Code.ELEM_TYPE) {
			Expression e1 = readExpression(bytes);
			Expression e = new ELEMTYPE(e1);
			return e;
		} else if (_byte == Code.RESULT) {
			Expression e = RESULT._RESULT;
			return e;
		} 
//		else if (_byte == Code.ALL_ARRAY_ELEM) {
//			Expression e = AllArrayElem.ALLARRAYELEM;
//			return e;
//		} 
		else if (_byte == Code._type) {
			JavaType javaType = readJavaType(bytes);
			Expression _type = new _TYPE(javaType);
			return _type;
		} else if (_byte == Code.TYPE) {
			Expression TYPE = JML_CONST_TYPE.JML_CONST_TYPE;
			return TYPE;
		} else if (_byte == Code.ARRAY_ACCESS) {
			Expression array = readExpression(bytes);
			Expression arrIndex = readExpression(bytes);
			Expression arrAccess = new ArrayAccessExpression(array, arrIndex);
			return arrAccess;
		} else if (_byte == Code.METHOD_CALL) {
			// what to do here - there is not encoding offered for the method references
			// methodRef expression n expression^n
			BCConstant mRef = (BCConstantMethodRef)readExpression(bytes);
			Expression ref = readExpression(bytes);
			int numberArgs = readShort(bytes);
			Expression[] args = new Expression[numberArgs];
			for (int i = 0; i < numberArgs; i++) {
				args[i] = readExpression(bytes);
			}
			return null;
			// here should be substituted with the specification of the called method with the needed substitutions
		} else if (_byte == Code.CAST) {
			JavaType type = readJavaType(bytes);
			Expression expr = readExpression(bytes);
			CastExpression castExpr = new CastExpression(type, expr);
			return castExpr;
		} else if (_byte == Code.FULL_QUALIFIED_NAME) { // .
			Expression expr = readExpression(bytes);
			Expression constant = readExpression(bytes);
			
			if (constant instanceof BCConstantFieldRef) {
				BCConstantFieldRef fCp = (BCConstantFieldRef) constant;
				Expression fieldAccessExpr =
					new FieldAccess(fCp, expr);
				return fieldAccessExpr;
			}
			// else null; e.i. if a qualified  name is found it must a field access expression
			return null;
		} else if (_byte == Code.BOOLEAN_EXPR) { // ? :
			Formula condition = readFormula(bytes);
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			ConditionalExpression conditionExpr =
				new ConditionalExpression(condition, expr1, expr2);
			return conditionExpr;
		} else if (_byte == Code.THIS) { // this expression 
			Expression _this = localVariables[0];
			return _this;
		} else if (_byte == Code.OLD_THIS) {
			Expression oldThis = new OLD(localVariables[0]);
			return oldThis;
		} else if (_byte == Code.NULL) {
			return NULL._NULL;
		} else if (
			(_byte == Code.OLD_FIELD_REF)
				|| (_byte == Code.OLD_JML_MODEL_FIELD)) {
			// see in the file remarks
			Expression fieldAccessExpression = readExpression(bytes);
			OLD oldFieldRef = new OLD(fieldAccessExpression);
			return oldFieldRef;
		} else if (_byte == Code.LOCAL_VARIABLE) {
			// the index of the local variable 
			int ind = readShort(bytes);
			Expression lVarAccess = localVariables[ind];
			return lVarAccess;
		} else if (_byte == Code.OLD_LOCAL_VARIABLE) {
			// the index of the local variable
			int ind = readShort(bytes);
			Expression lVarAccess = localVariables[ind];
			Expression oldValue = new OLD(lVarAccess);
			return oldValue;
		} else if (_byte == Code.ARRAYLENGTH) {
			ArrayLengthConstant length = ArrayLengthConstant.ARRAYLENGTHCONSTANT;
			return length;
		} else if (_byte == Code.FIELD_REF) {
			// read the index of the field_ref in the constant pool
//			int cpIndex = readShort(bytes);
			int cpIndex = readShort(bytes);
			// find the object in the constant field
			BCConstant constantField = constantPool.getConstant(cpIndex);
			if (!(constantField instanceof BCConstantFieldRef)) {
				throw new ReadAttributeException(
					"Error reading in the Constant Pool : reason : CONSTANT_Fieldref  expected at index "
						+ cpIndex);
			}
			return constantField;
		} else if (_byte == Code.JML_MODEL_FIELD) {
//			int cpIndex = readShort(bytes);
			int cpIndex = readShort(bytes);
			BCConstant constantField = constantPool.getConstant(cpIndex);
			if (!(constantField instanceof BCConstantFieldRef)) {
				throw new ReadAttributeException(
					"Error reading in the Constant Pool :reason :  CONSTANT_Fieldref expected for a model field ref at index "
						+ cpIndex);
			}
			return constantField;
		} else if (_byte == Code.METHOD_REF) {
			int cpIndex = readShort(bytes);
			BCConstant consantMethodRef = constantPool.getConstant(cpIndex);
			if (!(consantMethodRef instanceof BCConstantMethodRef)) {
				throw new ReadAttributeException(
					"Error reading in the Constant Pool :  reason: CONSTANT_Methodref  expected  at index "
						+ cpIndex);
			}
			return consantMethodRef;
		} else if (_byte == Code.JAVA_TYPE) {
			int cpIndex = readShort(bytes);
			BCConstant constantUtf8 = constantPool.getConstant(cpIndex);
			if (!(constantUtf8 instanceof BCConstantUtf8)) {
				throw new ReadAttributeException(
					"Error reading in the Constant Pool : reason:   CONSTANT_Utf8  expected  at index "
						+ cpIndex);
			}
			return constantUtf8;
		} else if ( _byte == Code.BOUND_VAR) {
			int ind = readByte(bytes);
			Variable var = new Variable(ind);  
			return var;
		} else if ( _byte == Code.STACK) {
			ArithmeticExpression counter = (ArithmeticExpression)readExpression(bytes);
			Stack stack = new Stack(counter);   
			return stack;
		} else if ( _byte == Code.STACK_COUNTER) {
			Counter c = Counter.getCounter();
			return c;
		} 
		// may be there should be translation for strings
		return null;
	}
    
    
    

/*	*//**
	 * reads the encoding of a cp constant 
	 * @param bytes
	 * @return
	 *//*
	private static final BCConstant readConstant(byte[] bytes)
		throws ReadAttributeException {
		int _byte = readByte(bytes);
		if (_byte == Code.ARRAYLENGTH) {
			ArrayLengthConstant length = new ArrayLengthConstant();
			return length;
		} else if (_byte == Code.FIELD_REF) {
			// read the index of the field_ref in the constant pool
//			int cpIndex = readShort(bytes);
			int cpIndex = readShort(bytes);
			// find the object in the constant field
			BCConstant constantField = constantPool.getConstant(cpIndex);
			if (!(constantField instanceof BCConstantFieldRef)) {
				throw new ReadAttributeException(
					"Error reading in the Constant Pool : reason : CONSTANT_Fieldref  expected at index "
						+ cpIndex);
			}
			return constantField;
		} else if (_byte == Code.JML_MODEL_FIELD) {
//			int cpIndex = readShort(bytes);
			int cpIndex = readShort(bytes);
			BCConstant constantField = constantPool.getConstant(cpIndex);
			if (!(constantField instanceof BCConstantFieldRef)) {
				throw new ReadAttributeException(
					"Error reading in the Constant Pool :reason :  CONSTANT_Fieldref expected for a model field ref at index "
						+ cpIndex);
			}
			return constantField;
		} else if (_byte == Code.METHOD_REF) {
			int cpIndex = readShort(bytes);
			BCConstant consantMethodRef = constantPool.getConstant(cpIndex);
			if (!(consantMethodRef instanceof BCConstantMethodRef)) {
				throw new ReadAttributeException(
					"Error reading in the Constant Pool :  reason: CONSTANT_Methodref  expected  at index "
						+ cpIndex);
			}
			return consantMethodRef;
		} else if (_byte == Code.JAVA_TYPE) {
			int cpIndex = readShort(bytes);
			BCConstant constantUtf8 = constantPool.getConstant(cpIndex);
			if (!(constantUtf8 instanceof BCConstantUtf8)) {
				throw new ReadAttributeException(
					"Error reading in the Constant Pool : reason:   CONSTANT_Utf8  expected  at index "
						+ cpIndex);
			}
			return constantUtf8;
		}
		// may be there should be translation for strings
		return null;
	}*/

	//	private static final Expression readJavaExpression(byte[] bytes) {
	//		return null;
	//	}

	/**
	 * @param bytes
	 * @return
	 */
	private static JavaType readJavaType(byte[] bytes)
		throws ReadAttributeException {
		Expression constant = readExpression(bytes);
		if (!(constant instanceof BCConstantUtf8)) {
			throw new ReadAttributeException(
				" Error reading a JavaType : reason : expected Constant Utf8 Info structure in the constant pool  at index "
					+ ((BCConstant)constant).getCPIndex());
		}
		BCConstantUtf8 CONSTANT_Class = (BCConstantUtf8) constant;
		String name = CONSTANT_Class.getLiteral().toString();
		JavaType type = JavaType.getJavaType(name);
		return type;
	}
}
