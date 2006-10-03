/*
 * Created on Jul 8, 2004
 *
 * this class reads user an array of bytes and parses it 
 * into BML specification 
 */
package bytecode_wp.bc.io;

import java.io.ByteArrayInputStream;
import java.io.DataInputStream;
import java.io.IOException;

import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Unknown;

import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcclass.attributes.Assert;
import bytecode_wp.bcclass.attributes.AssertTable;
import bytecode_wp.bcclass.attributes.BCAttribute;
import bytecode_wp.bcclass.attributes.BCLineNumber;
import bytecode_wp.bcclass.attributes.BlockSpecification;
import bytecode_wp.bcclass.attributes.ClassInvariant;
import bytecode_wp.bcclass.attributes.Exsures;
import bytecode_wp.bcclass.attributes.ExsuresTable;
import bytecode_wp.bcclass.attributes.HistoryConstraints;
import bytecode_wp.bcclass.attributes.LoopSpecification;
import bytecode_wp.bcclass.attributes.MethodSpecification;
import bytecode_wp.bcclass.attributes.ModifiesSet;
import bytecode_wp.bcclass.attributes.Postcondition;
import bytecode_wp.bcclass.attributes.SET;
import bytecode_wp.bcclass.attributes.SETTable;
import bytecode_wp.bcclass.attributes.SecondConstantPool;
import bytecode_wp.bcclass.attributes.SingleBlockSpecification;
import bytecode_wp.bcclass.attributes.SingleLoopSpecification;
import bytecode_wp.bcclass.attributes.SpecificationCase;
import bytecode_wp.bcexpression.ArithmeticExpression;
import bytecode_wp.bcexpression.ArrayAccessExpression;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.BitExpression;
import bytecode_wp.bcexpression.CastExpression;
import bytecode_wp.bcexpression.ConditionalExpression;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.ExpressionConstants;
import bytecode_wp.bcexpression.FieldAccess;
import bytecode_wp.bcexpression.MethodInvocation;
import bytecode_wp.bcexpression.NULL;
import bytecode_wp.bcexpression.NumberLiteral;
import bytecode_wp.bcexpression.Variable;
import bytecode_wp.bcexpression.javatype.JavaObjectType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.jml.ELEMTYPE;
import bytecode_wp.bcexpression.jml.JML_CONST_TYPE;
import bytecode_wp.bcexpression.jml.OLD;
import bytecode_wp.bcexpression.jml.RESULT;
import bytecode_wp.bcexpression.jml.TYPEOF;
import bytecode_wp.bcexpression.jml._TYPE;
import bytecode_wp.bcexpression.vm.Counter;
import bytecode_wp.bcexpression.vm.Stack;
import bytecode_wp.constants.ArrayLengthConstant;
import bytecode_wp.constants.BCConstant;
import bytecode_wp.constants.BCConstantFieldRef;
import bytecode_wp.constants.BCConstantMethodRef;
import bytecode_wp.constants.BCConstantUtf8;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.formula.Quantificator;
import bytecode_wp.modifexpression.AllArrayElem;
import bytecode_wp.modifexpression.ArrayElemFromTo;
import bytecode_wp.modifexpression.Everything;
import bytecode_wp.modifexpression.ModifiesArray;
import bytecode_wp.modifexpression.ModifiesDOT;
import bytecode_wp.modifexpression.ModifiesExpression;
import bytecode_wp.modifexpression.ModifiesIdent;
import bytecode_wp.modifexpression.ModifiesLocalVariable;
import bytecode_wp.modifexpression.Nothing;
import bytecode_wp.modifexpression.SingleIndex;
import bytecode_wp.modifexpression.SpecArray;

/**
 * @author mpavlova
 * 
 * the class represents a parser for the
 */
public class AttributeReader {
	private static int pos;

	private static BCClass clazz;

	
	//private static BCLineNumber[] lineNumberTable;

	private static BCLocalVariable[] localVariables;

	public static final int ERROR_READING_OUT_OF_ARR = -1;

	
	/**
	 * @deprecated use {@link #readAttribute(Unknown, BCClass, BCLocalVariable[])}
	 *  	instead
	 */
	public static BCAttribute readAttribute(Unknown privateAttr,
			BCClass _clazz, BCLineNumber[] _lineNumberTable,
			BCLocalVariable[] _localVariables) throws ReadAttributeException {
		
		// Commented by jgc: lineNumberTable useless?
		//lineNumberTable = _lineNumberTable;
		return readAttribute(privateAttr, _clazz, _localVariables);
		
	}
	
	public static BCAttribute readAttribute(Unknown privateAttr,
			BCClass _clazz, BCLocalVariable[] _localVariables) 
				throws ReadAttributeException {
		clazz = _clazz;
		/* constantPool = _clazz.getConstantPool(); */
		

		localVariables = _localVariables;
		String name = privateAttr.getName();
		if (name.equals(BCAttribute.ASSERT)) {
			return readAssertTable(privateAttr.getBytes());
		}
		if (name.equals(BCAttribute.SET)) {
			return readSetTable(privateAttr.getBytes());
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
		if (name.equals(BCAttribute.SECOND_CONSTANT_POOL)) {
			return readSecondConstantPool(privateAttr.getBytes());
		}
		return null;
	}

	// /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// ////////////////////////////////////Class
	// Specification/////////////////////////////////////////////
	// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	private static HistoryConstraints readHistoryConstraints(byte[] bytes)
			throws ReadAttributeException {
		// here the length of the attribute not needed
		pos = 0;
		Formula predicate = (Formula) readExpression(bytes);
		HistoryConstraints historyConstraints = new HistoryConstraints(
				predicate);
		return historyConstraints;
	}

	private static ClassInvariant readClassInvariant(byte[] bytes)
			throws ReadAttributeException {
		// here the length of the attribute not needed
		pos = 0;
		Formula predicate = (Formula) readExpression(bytes);
		ClassInvariant classInvariant = new ClassInvariant(predicate, JavaType
				.getJavaType(clazz.getName()), ClassInvariant.INSTANCE);
		return classInvariant;
	}
	
	private static SecondConstantPool readSecondConstantPool(byte[] bytes) throws ReadAttributeException {
		try {
			return new SecondConstantPool(new DataInputStream(new ByteArrayInputStream(bytes)));
		} catch (IOException e) {
			return null;
		}
	}

	// ////////////////////////////////////////end Class
	// specification//////////////////////////////////////

	// //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// ////////////////////////////////////Method
	// Specification/////////////////////////////////////////////
	// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	// //////////////////// start : block specification
	// /////////////////////////////////////////////////
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
							+ attributes_count + " and attribute length =  "
							+ attribute_length);
		}
		SingleBlockSpecification[] blockSpecs = new SingleBlockSpecification[attributes_count];
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
	private static SingleBlockSpecification readSingleBlockSpecification(
			byte[] bytes) throws ReadAttributeException {
		int startCpInd = readShort(bytes);
		int endCpInd = readShort(bytes);
		Formula precondition = (Formula) readExpression(bytes);
		int modifiesCount = readShort(bytes);
		Expression[] modifies = null;
		if (modifiesCount > 0) {
			modifies = new Expression[modifiesCount];
			for (int i = 0; i < modifiesCount; i++) {
				modifies[i] = readExpression(bytes);
			}
		}
		Formula postcondition = (Formula) readExpression(bytes);
		SingleBlockSpecification blockSpec = new SingleBlockSpecification(
				startCpInd, endCpInd, precondition, modifies, postcondition);
		return blockSpec;
	}

	// //////////////////// end : block specification
	// /////////////////////////////////////////////////

	// //////////////////// start : loopspecifcation
	// /////////////////////////////////////////////////

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
							+ attributes_count + " and attribute length  = "
							+ attribute_length);
		}
		SingleLoopSpecification[] loopSpecs = new SingleLoopSpecification[attributes_count];
		for (int i = 0; i < attributes_count; i++) {
			if (pos >= attribute_length) {
				throw new ReadAttributeException(
						"uncorrect LoopSpecification  attribute attribute_length "
								+ attribute_length
								+ " <  actual length of attribute ");
			}
			loopSpecs[i] = readSingleLoopSpecification(bytes);
		}
		LoopSpecification loopSpe = new LoopSpecification(loopSpecs);
		return loopSpe;
	}

	private static SingleLoopSpecification readSingleLoopSpecification(
			byte[] bytes) throws ReadAttributeException {
		int loopIndex = readShort(bytes);
		ModifiesSet modifies = readModifies(bytes);
		Expression invariant = readExpression(bytes);
		Expression decreases = readExpression(bytes);
		SingleLoopSpecification loopSpec = new SingleLoopSpecification(
				loopIndex, modifies, (Formula) invariant, decreases);
		return loopSpec;
	}

	// //////////////////// end : loopspecifcation
	// /////////////////////////////////////////////////

	// ////////////////////// start : set
	// table/////////////////////////////////////////////////

	/**
	 * the method reads an array of set model statements. In Jml this statements
	 * are of the form: set a = expr where a is a ghost variable
	 */
	private static SETTable readSetTable(byte[] bytes)
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
		SET[] sets = new SET[attributes_count];
		for (int i = 0; i < attributes_count; i++) {
			if (pos >= attribute_length) {
				throw new ReadAttributeException(
						"uncorrect Assert  attribute attribute_length "
								+ attribute_length
								+ " <  actual length of attribute ");
			}
			sets[i] = readSet(bytes);
		}
		SETTable setTable = new SETTable(sets);
		return setTable;
	}

	/**
	 * @param pos -
	 *            the position from which starts the assert object
	 * @param bytes
	 *            -the array from which the assert object is read
	 * @param assert -
	 *            an object that should be initialised by the method
	 * @return an object of type <code>bcclass.attributes.SET</code>
	 */
	private static SET readSet(byte[] bytes) throws ReadAttributeException {
		int pcIndex = readShort(bytes);
		Expression jmlExprToAssign = readExpression(bytes);
		Expression exprAssign = readExpression(bytes);
		return new SET(pcIndex, jmlExprToAssign, exprAssign);
	}

	// /////////////////////end : set table
	// /////////////////////////////////////////////////

	// //////////////////// start : assert table
	// /////////////////////////////////////////////////
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
	 * @param pos -
	 *            the position from which starts the assert object
	 * @param bytes
	 *            -the array from which the assert object is read
	 * @param assert -
	 *            an object that should be initialised by the method
	 * @return the leftmost index into the byte array bytes that is not read by
	 *         the method
	 */
	private static Assert readAssert(byte[] bytes)
			throws ReadAttributeException {
		int pcIndex = readShort(bytes);
		Formula formula = (Formula) readExpression(bytes);
		return new Assert(formula, pcIndex);
	}

	// //////////////////// end : assert table
	// /////////////////////////////////////////////////

	// //////////////// start : method specification
	// /////////////////////////////////////////////////

//use undetermined...	
//	private static MethodInvocation readMethodInvocation(byte[] bytes)
//			throws ReadAttributeException {
//		return null;
//	}

	private static MethodSpecification readMethodSpecification(byte[] bytes)
			throws ReadAttributeException {
		pos = 0;
		int attribute_length = bytes.length;
		Formula precondition = (Formula) readExpression(bytes);
		int attributes_count = readAttributeCount(bytes);
		if (attribute_length <= 0) {
			return null;
		}
		if (attributes_count <= 0) {
			throw new ReadAttributeException(
					"a wrong MethodSpecification  attribute : attribute count  = "
							+ attributes_count + " and attribute length  =  "
							+ attribute_length + "  ");
		}
		SpecificationCase[] specCases = new SpecificationCase[attributes_count];
		for (int i = 0; i < attributes_count; i++) {
			specCases[i] = readSpecificationCase(bytes);
		}
		MethodSpecification methodSpec = new MethodSpecification(precondition,
				specCases);
		return methodSpec;
	}

	private static SpecificationCase readSpecificationCase(byte[] bytes)
			throws ReadAttributeException {
		Formula precondition = (Formula) readExpression(bytes);
		ModifiesSet modifies = readModifies(bytes);

		Formula postcondition = (Formula) readExpression(bytes);
		ExsuresTable exsures = readExsuresTable(bytes);
		SpecificationCase specCase = new SpecificationCase(precondition,
				new Postcondition(postcondition), modifies, exsures);
		return specCase;
	}

	/**
	 * @param bytes
	 * @return
	 */
	private static ModifiesSet readModifies(byte[] bytes)
			throws ReadAttributeException {
		int modifiesCount = readAttributeCount(bytes);
		ModifiesExpression[] modifies = null;

		if (modifiesCount > 0) {
			modifies = new ModifiesExpression[modifiesCount];
			for (int i = 0; i < modifiesCount; i++) {
				modifies[i] = readModifiesExpression(bytes);
			}
		}
		if (modifies == null) {
			ModifiesSet modifSet = new ModifiesSet(
					new ModifiesExpression[] { new Everything() }, clazz);
			return modifSet;
		}
		ModifiesSet modifSet = new ModifiesSet(modifies, clazz);
		return modifSet;
	}

	private static ModifiesExpression readModifiesExpression(byte[] bytes)
			throws ReadAttributeException {
		int _byte = readByte(bytes);
		if (_byte == Code.MODIFIES_NOTHING) {
			return Nothing.NOTHING;
		}
		if (_byte == Code.MODIFIES_EVERYTHING) {
			return new Everything();
		}
		if (_byte == Code.MODIFIES_IDENT) {
			Expression e = readExpression(bytes);
			if (e instanceof BCLocalVariable) {
				ModifiesLocalVariable modifLocVar = new ModifiesLocalVariable(
						(BCLocalVariable) e, clazz);
				return modifLocVar;
			}
			ModifiesIdent modifId = new ModifiesIdent(e, clazz);
			return modifId;
		}
		if (_byte == Code.MODIFIES_DOT) {
			ModifiesExpression ident = readModifiesExpression(bytes);
			Expression expr = readExpression(bytes);
			ModifiesDOT modifDot = new ModifiesDOT(ident, expr, clazz);
			return modifDot;
		}
		if (_byte == Code.MODIFIES_ARRAY) {
			ModifiesExpression arrExpr = readModifiesExpression(bytes);
			SpecArray specArray = readSpecArray(bytes);
			ModifiesArray modArray = new ModifiesArray(arrExpr, specArray,
					clazz);
			return modArray;
		}
		return null;
	}

	private static SpecArray readSpecArray(byte[] bytes)
			throws ReadAttributeException {
		int _byte = readByte(bytes);

		if (_byte == Code.MODIFIES_SINGLE_INDICE) {
			Expression singleIndice = readExpression(bytes);
			SingleIndex index = new SingleIndex(singleIndice);
			return index;
		}
		if (_byte == Code.MODIFIES_INTERVAL) {
			Expression start = readExpression(bytes);
			Expression end = readExpression(bytes);
			ArrayElemFromTo interval = new ArrayElemFromTo(start, end);
			return interval;
		}
		if (_byte == Code.MODIFIES_STAR) {
			return AllArrayElem.ALLARRAYELEM;
		}
		return null;
	}

	/**
	 * reads an exsures table
	 * 
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
		Formula exsFormula = (Formula) readExpression(bytes);
		Exsures exsures = new Exsures(exsFormula, excType);
		return exsures;
	}

	// ////////////////// end : method specification
	// /////////////////////////////////////////////////

	// //////////////////////////////////////////////////////////////////////////////////////////////////////////////
	// ////////////////////////////////Expressions and Formulas
	// ///////////////////////////////////////////////////////////////
	// /////////////////////////////////////////////////////////////////////////////////////////////////////////////
// jgc: use undetermined...
//	private static int readAttributeLength(byte[] bytes) {
//		int attribute_length = readInt(bytes);
//		return attribute_length;
//	}

	private static int readAttributeCount(byte[] bytes) {
		int attribute_count = readShort(bytes);
		return attribute_count;
	}

	private static int readInt(byte[] bytes) {
		int integer = ((bytes[pos] & 0xff) << 24)
				| ((bytes[pos + 1] & 0xff) << 16)
				| ((bytes[pos + 2] & 0xff) << 8) | (bytes[pos + 3] & 0xff);
		pos = pos + 4;
		return integer;
	}

	private static int readShort(byte[] bytes) {
		int _short = ((bytes[pos] & 0xff) << 8) | (bytes[pos + 1] & 0xff);
		pos = pos + 2;
		return _short;
	}

	private static int readChar(byte[] bytes) {
		int _char = (int) ((bytes[pos] << 8) | (bytes[pos + 1] & 0xff));
		pos = pos + 2;
		return _char;
	}

	private static int readByte(byte[] bytes) {
		// Util.dump("pos = " + pos );
		if (pos >= bytes.length) {
			return ERROR_READING_OUT_OF_ARR;
		}
		int _byte = bytes[pos] & 0xff;
		pos = pos + 1;
		return _byte;
	}

/*	*//**
	 * @param bytes - byte array containing the encoding of a user defined class
	 * 	attribute 
	 * @param p - 
	 * @return  the value in the array byted at position pos
	 *//*
	private static int checkByteValue(byte[] bytes, int p) {
		int _byte = bytes[p] & 0xff;
		return _byte;
	}*/

	private static Expression readExpression(byte[] bytes)
			throws ReadAttributeException {
		int _byte = readByte(bytes);
		if (_byte == Code.PLUS) { // ARithmetic
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = ArithmeticExpression.getArithmeticExpression(e1, e2,
					ExpressionConstants.ADD);
			return e;
		} else if (_byte == Code.MINUS) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = ArithmeticExpression.getArithmeticExpression(e1, e2,
					ExpressionConstants.SUB);
			return e;
		} else if (_byte == Code.MULT) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = ArithmeticExpression.getArithmeticExpression(e1, e2,
					ExpressionConstants.MULT);
			return e;
		} else if (_byte == Code.DIV) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = ArithmeticExpression.getArithmeticExpression(e1, e2,
					ExpressionConstants.DIV);
			return e;
		} else if (_byte == Code.REM) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = ArithmeticExpression.getArithmeticExpression(e1, e2,
					ExpressionConstants.REM);
			return e;
		} else if (_byte == Code.NEG) {
			Expression e1 = readExpression(bytes);
			Expression e = ArithmeticExpression.getArithmeticExpression(e1,
					ExpressionConstants.NEG);
			return e;
		} else if (_byte == Code.BITWISEAND) { // Bitwise
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = new BitExpression(e1, e2,
					ExpressionConstants.BITWISEAND);
			return e;
		} else if (_byte == Code.BITWISEOR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = new BitExpression(e1, e2,
					ExpressionConstants.BITWISEOR);
			return e;
		} else if (_byte == Code.BITWISEXOR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = new BitExpression(e1, e2,
					ExpressionConstants.BITWISEXOR);
			return e;
		} else if (_byte == Code.SHL) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
			// e1 the expression that is shifted
			// e2 is the number of positions e1 to shift with
			new BitExpression(e1, e2, ExpressionConstants.SHL);
			return e;
		} else if (_byte == Code.SHR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
			// e1 the expression that is shifted
			// e2 is the number of positions e1 to shift with
			new BitExpression(e1, e2, ExpressionConstants.SHR);
			return e;
		} else if (_byte == Code.USHR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
			// e1 the expression that is shifted
			// e2 is the number of positions e1 to shift with
			new BitExpression(e1, e2, ExpressionConstants.USHR);
			return e;
		} else if (_byte == Code.INT_LITERAL) { // Literals
			int literal = readInt(bytes);
			Expression e = new NumberLiteral(literal);
			return e;
		} else if (_byte == Code.CHAR_LITERAL) {
			int literal = readChar(bytes);

			Expression e = new NumberLiteral(literal);
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
			if (array instanceof OLD) {
				array = ((OLD) array).getSubExpressions()[0];
				if (arrIndex instanceof OLD) {
					arrIndex = ((OLD) arrIndex).getSubExpressions()[0];
				}
				Expression fieldAccessExpr = new OLD(new ArrayAccessExpression(
						array, arrIndex));
				return fieldAccessExpr;
			}

			Expression arrAccess = new ArrayAccessExpression(array, arrIndex);
			return arrAccess;
		} else if (_byte == Code.METHOD_CALL) {
			// what to do here - there is not encoding offered for the method
			// references
			// methodRef expression n expression^n
			BCConstantMethodRef mRef = (BCConstantMethodRef) readExpression(bytes);
			Expression ref = readExpression(bytes);
			int numberArgs = readShort(bytes);
			Expression[] subExpr = new Expression[numberArgs + 1];
			subExpr[0] = ref;

			for (int i = 0; i < numberArgs; i++) {
				subExpr[i + 1] = readExpression(bytes);
			}
//		commented by jgc: what's its use?
//			String clazz_name = ((BCConstantClass) (clazz.getConstantPool()
//					.getConstant(mRef.getClassIndex()))).getName();

			MethodInvocation methInv = new MethodInvocation(mRef, subExpr);
			return methInv;
			// here should be substituted with the specification of the called
			// method with the needed substitutions
		} else if (_byte == Code.CAST) {
			JavaType type = readJavaType(bytes);
			Expression expr = readExpression(bytes);
			CastExpression castExpr = new CastExpression(type, expr);
			return castExpr;
		} else if (_byte == Code.FULL_QUALIFIED_NAME) { // .
			Expression expr = readExpression(bytes);
			Expression constant = readExpression(bytes);
			if (constant instanceof OLD) {
				constant = ((OLD) constant).getSubExpressions()[0];
				if (expr instanceof OLD) {
					expr = ((OLD) expr).getSubExpressions()[0];
				}
				Expression fieldAccessExpr = new OLD(new FieldAccess(constant,
						expr));
				return fieldAccessExpr;
			}
			Expression fieldAccessExpr = new FieldAccess(constant, expr);
			return fieldAccessExpr;
			/*
			 * if (constant instanceof BCConstantFieldRef) { BCConstantFieldRef
			 * fCp = (BCConstantFieldRef) constant; Expression fieldAccessExpr =
			 * new FieldAccess(fCp, expr); return fieldAccessExpr; }
			 */
			// else null; e.i. if a qualified name is found it must a field
			// access expression
		} else if (_byte == Code.BOOLEAN_EXPR) { // ? :
			Formula condition = (Formula) readExpression(bytes);
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			ConditionalExpression conditionExpr = new ConditionalExpression(
					condition, expr1, expr2);
			return conditionExpr;
		} else if (_byte == Code.THIS) { // this expression
			Expression _this = localVariables[0];
			return _this;
		} else if (_byte == Code.OLD_THIS) {
			Expression oldThis = new OLD(localVariables[0]);
			return oldThis;
		} else if (_byte == Code.NULL) {
			return NULL._NULL;
		} else if ((_byte == Code.OLD_FIELD_REF)
				|| (_byte == Code.OLD_JML_MODEL_FIELD)) {
			// see in the file remarks
			int cpIndex = readShort(bytes);
			// find the object in the constant field
			BCConstant constantField = clazz.getConstantPool().getConstant(
					cpIndex);
			if (!(constantField instanceof BCConstantFieldRef)) {
				throw new ReadAttributeException(
						"Error reading in the Constant Pool : reason : CONSTANT_Fieldref  expected at index "
								+ cpIndex);
			}
			Expression oldFieldRef = new OLD(constantField);
			return oldFieldRef;
		} else if (_byte == Code.LOCAL_VARIABLE) {
			// the index of the local variable
			int ind = readShort(bytes);
			if (localVariables.length <= ind) {
				throw new ArrayIndexOutOfBoundsException();
			}
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
		} else if (_byte == Code.FIELD_LOC) {
			// read the index of the field_ref in the constant pool
			int cpIndex = readShort(bytes);
			// find the object in the constant field
			BCConstant constantField = clazz.getConstantPool().getConstant(
					cpIndex);
			if (!(constantField instanceof BCConstantFieldRef)) {
				throw new ReadAttributeException(
						"Error reading in the Constant Pool : reason : CONSTANT_Fieldref  expected at index "
								+ cpIndex);
			}
			return constantField;
		} else if (_byte == Code.JML_MODEL_FIELD) {
			int cpIndex = readShort(bytes);
			BCConstant constantField = clazz.getConstantPool().getConstant(
					cpIndex);
			if (!(constantField instanceof BCConstantFieldRef)) {
				throw new ReadAttributeException(
						"Error reading in the Constant Pool :reason :  CONSTANT_Fieldref expected for a model field ref at index "
								+ cpIndex);
			}
			return constantField;
		} else if (_byte == Code.METHOD_REF) {
			int cpIndex = readShort(bytes);
			BCConstant consantMethodRef = clazz.getConstantPool().getConstant(
					cpIndex);
			if (!(consantMethodRef instanceof BCConstantMethodRef)) {
				throw new ReadAttributeException(
						"Error reading in the Constant Pool :  reason: CONSTANT_Methodref  expected  at index "
								+ cpIndex);
			}
			return consantMethodRef;
		} else if (_byte == Code.JAVA_TYPE) {
			int cpIndex = readShort(bytes);
			BCConstant constantUtf8 = clazz.getConstantPool().getConstant(
					cpIndex);
			if (!(constantUtf8 instanceof BCConstantUtf8)) {
				throw new ReadAttributeException(
						"Error reading in the Constant Pool : reason:   CONSTANT_Utf8  expected  at index "
								+ cpIndex);
			}
			return constantUtf8;
		} else if (_byte == Code.BOUND_VAR) {
			int ind = readShort(bytes);
			Variable var = new Variable(ind);
			return var;
		} else if (_byte == Code.STACK) {
			ArithmeticExpression counter = (ArithmeticExpression) readExpression(bytes);
			Stack stack = new Stack(counter);
			return stack;
		} else if (_byte == Code.STACK_COUNTER) {
			Counter c = Counter.getCounter();
			return c;
		} else if (_byte == Code.TRUE) {
			return Predicate0Ar.TRUE;
		} else if (_byte == Code.FALSE) {
			return Predicate0Ar.FALSE;
		} else if (_byte == Code.AND) {
			Expression f1 = readExpression(bytes);
			Expression f2 = readExpression(bytes);
			Formula formula = Formula.getFormula(f1, f2, Connector.AND);
			return formula;

			/* Formula f2 =(Formula) readExpression(bytes); */

		} else if (_byte == Code.OR) {
			Expression f1 = readExpression(bytes);
			Expression f2 = readExpression(bytes);
			Formula formula = Formula.getFormula(f1, f2, Connector.OR);
			return formula;
		} else if (_byte == Code.IMPLIES) {
			Expression f1 = readExpression(bytes);
			Expression f2 = readExpression(bytes);
			Formula formula = Formula.getFormula(f1, f2, Connector.IMPLIES);

			return formula;
		} else if (_byte == Code.NOT) {
			Expression f1 = readExpression(bytes);
			if (f1 instanceof Formula) {
				Formula formula = Formula.getFormula((Formula) f1,
						Connector.NOT);
				return formula;
			}
			DesugarNegBoolExpr des = new DesugarNegBoolExpr(f1, true);
			return des;
		} else if (_byte == Code.GRT) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate = Predicate2Ar.getPredicate(expr1, expr2,
					PredicateSymbol.GRT);
			return predicate;
		} else if (_byte == Code.GRTEQ) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate = Predicate2Ar.getPredicate(expr1, expr2,
					PredicateSymbol.GRTEQ);
			return predicate;
		} else if (_byte == Code.LESS) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate = Predicate2Ar.getPredicate(expr1, expr2,
					PredicateSymbol.LESS);
			return predicate;
		} else if (_byte == Code.LESSEQ) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate = Predicate2Ar.getPredicate(expr1, expr2,
					PredicateSymbol.LESSEQ);
			return predicate;
		} else if (_byte == Code.EQ) {
			Expression expr1 = readExpression(bytes);
			// here we substitute the appearing formulas in equality relation
			// as the JVM do not support the boolean type, in place of the true
			// boolean value
			// 1 is used and in place of the false boolean value 0 is used
			// Thus suppose that expr1 is a formula. It is substituted with:
			// 1 if the formula is the predicate true
			// 0 if the formula is the predicate false
			// else if it is another type of formula and expr2 is not a formula:
			// f == expr2 is substituted with
			// 1 == expr2 ==> f /\ 0 == expr2 ==> !f
			// else if
			Formula f1 = null;
			DesugarNegBoolExpr des1 = null;
			if (expr1 == Predicate0Ar.TRUE) {
				expr1 = new NumberLiteral(1);
			} else if (expr1 == Predicate0Ar.FALSE) {
				expr1 = new NumberLiteral(0);
			} else if (expr1 instanceof Formula) {
				f1 = (Formula) expr1;
			} else if (expr1 instanceof DesugarNegBoolExpr) {
				des1 = (DesugarNegBoolExpr) expr1;
			}

			Expression expr2 = readExpression(bytes);
			Formula f2 = null;
			DesugarNegBoolExpr des2 = null;
			if (expr2 == Predicate0Ar.TRUE) {
				expr2 = new NumberLiteral(1);
			} else if (expr2 == Predicate0Ar.FALSE) {
				expr2 = new NumberLiteral(0);
			} else if (expr2 instanceof Formula) {
				f2 = (Formula) expr2;
			} else if (expr2 instanceof DesugarNegBoolExpr) {
				des2 = (DesugarNegBoolExpr) expr2;
			}
			if ((des2 != null) && (f1 == null) && (des1 == null)) {
				Formula posCondition = des2.getPositiveCondition();
				Expression posValue = des2.getPositiveValue();
				Formula expr2_eq_posValue = new Predicate2Ar(expr1, posValue,
						PredicateSymbol.EQ);
				Formula posCase = Formula.getFormula(posCondition,
						expr2_eq_posValue, Connector.EQUIV);

				return posCase;
				/*
				 * Formula negCondition = des2.getNegativeCondition();
				 * Expression negValue = des2.getNegativeValue(); Formula
				 * expr2_eq_negValue = new Predicate2Ar(expr1, negValue,
				 * PredicateSymbol.EQ ); Formula negCase = Formula.getFormula(
				 * negCondition, expr2_eq_negValue, Connector.IMPLIES); Formula
				 * posAndNeg = Formula.getFormula(posCase, negCase,
				 * Connector.AND); return posAndNeg;
				 */
			}
			if ((f1 != null) && (f2 != null)) {
				Formula f = Formula.getFormula(f1, f2, Connector.EQUIV);
				return f;
			} else if (f1 != null) {
				Formula true_eq_e2 = Predicate2Ar.getPredicate(
						new NumberLiteral(1), expr2, PredicateSymbol.EQ);
				Formula true_eq_e2_equiv_f1 = Formula.getFormula(true_eq_e2,
						f1, Connector.EQUIV);
				return true_eq_e2_equiv_f1;

				/*
				 * Formula false_eq_e2 = Predicate2Ar.getPredicate(new
				 * NumberLiteral(0), expr2, PredicateSymbol.EQ); Formula
				 * false_eq_e2_equiv_notf1 = Formula.getFormula(false_eq_e2,
				 * Formula.getFormula(f1, Connector.NOT), Connector.IMPLIES );
				 * 
				 * Formula equivalence = Formula.getFormula(true_eq_e2_equiv_f1,
				 * false_eq_e2_equiv_notf1, Connector.AND); return equivalence;
				 */
			} else if (f2 != null) {
				Formula true_eq_e1 = Predicate2Ar.getPredicate(expr1,
						new NumberLiteral(1), PredicateSymbol.EQ);
				Formula true_eq_e1_equiv_f2 = Formula.getFormula(true_eq_e1,
						f2, Connector.EQUIV);
				return true_eq_e1_equiv_f2;
				/*
				 * Formula false_eq_e1 = Predicate2Ar.getPredicate(expr1, new
				 * NumberLiteral(0), PredicateSymbol.EQ); Formula
				 * false_eq_e1_equiv_notf2 = Formula.getFormula(false_eq_e1,
				 * Formula.getFormula(f2, Connector.NOT), Connector.IMPLIES);
				 * 
				 * Formula equivalence = Formula.getFormula(true_eq_e1_equiv_f2,
				 * false_eq_e1_equiv_notf2, Connector.AND); return equivalence;
				 */
			} else {
				Formula predicate = Predicate2Ar.getPredicate(expr1, expr2,
						PredicateSymbol.EQ);
				return predicate;
			}

		} else if (_byte == Code.NOTEQ) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			Formula predicate = Formula.getFormula(Predicate2Ar.getPredicate(
					expr1, expr2, PredicateSymbol.EQ), Connector.NOT);
			return predicate;
		} else if (_byte == Code.INSTANCEOF) {
			Expression expr1 = readExpression(bytes);
			JavaType type = readJavaType(bytes);
			Formula predicate = new Predicate2Ar(type, expr1,
					PredicateSymbol.INSTANCEOF);
			return predicate;
		} else if (_byte == Code.SUBTYPE) {
			JavaType type1 = readJavaType(bytes);
			JavaType type2 = readJavaType(bytes);
			Formula predicate = new Predicate2Ar(type1, type2,
					PredicateSymbol.SUBTYPE);
			return predicate;

		}
		if (_byte == Code.EXISTS) {
			int numBoundVars = readByte(bytes);
			Variable[] vars = new Variable[numBoundVars];
			for (int i = 0; i < numBoundVars; i++) {
				JavaType jType = readJavaType(bytes);
				Variable var = new Variable(i, jType);
				vars[i] = var;
			}
			Quantificator exists = new Quantificator(Quantificator.EXISTS, vars);
			Formula f = (Formula) readExpression(bytes);
			Formula forallFormula = Formula.getFormula(f, exists);
			return forallFormula;

		} else if (_byte == Code.FORALL) {
			int numBoundVars = readByte(bytes);
			Variable[] vars = new Variable[numBoundVars];
			for (int i = 0; i < numBoundVars; i++) {
				JavaType jType = readJavaType(bytes);
				Variable var = new Variable(i, jType);
				vars[i] = var;
			}
			Quantificator forall = new Quantificator(Quantificator.FORALL, vars);
			Formula f = (Formula) readExpression(bytes);
			Formula forallFormula = Formula.getFormula(f, forall);
			return forallFormula;
		}
		return null;
	}

	/*	*//**
			 * reads the encoding of a cp constant
			 * 
			 * @param bytes
			 * @return
			 */
	/*
	 * private static final BCConstant readConstant(byte[] bytes) throws
	 * ReadAttributeException { int _byte = readByte(bytes); if (_byte ==
	 * Code.ARRAYLENGTH) { ArrayLengthConstant length = new
	 * ArrayLengthConstant(); return length; } else if (_byte == Code.FIELD_REF) { //
	 * read the index of the field_ref in the constant pool // int cpIndex =
	 * readShort(bytes); int cpIndex = readShort(bytes); // find the object in
	 * the constant field BCConstant constantField =
	 * constantPool.getConstant(cpIndex); if (!(constantField instanceof
	 * BCConstantFieldRef)) { throw new ReadAttributeException( "Error reading
	 * in the Constant Pool : reason : CONSTANT_Fieldref expected at index " +
	 * cpIndex); } return constantField; } else if (_byte ==
	 * Code.JML_MODEL_FIELD) { // int cpIndex = readShort(bytes); int cpIndex =
	 * readShort(bytes); BCConstant constantField =
	 * constantPool.getConstant(cpIndex); if (!(constantField instanceof
	 * BCConstantFieldRef)) { throw new ReadAttributeException( "Error reading
	 * in the Constant Pool :reason : CONSTANT_Fieldref expected for a model
	 * field ref at index " + cpIndex); } return constantField; } else if (_byte ==
	 * Code.METHOD_REF) { int cpIndex = readShort(bytes); BCConstant
	 * consantMethodRef = constantPool.getConstant(cpIndex); if
	 * (!(consantMethodRef instanceof BCConstantMethodRef)) { throw new
	 * ReadAttributeException( "Error reading in the Constant Pool : reason:
	 * CONSTANT_Methodref expected at index " + cpIndex); } return
	 * consantMethodRef; } else if (_byte == Code.JAVA_TYPE) { int cpIndex =
	 * readShort(bytes); BCConstant constantUtf8 =
	 * constantPool.getConstant(cpIndex); if (!(constantUtf8 instanceof
	 * BCConstantUtf8)) { throw new ReadAttributeException( "Error reading in
	 * the Constant Pool : reason: CONSTANT_Utf8 expected at index " + cpIndex); }
	 * return constantUtf8; } // may be there should be translation for strings
	 * return null; }
	 */

	// private static final Expression readJavaExpression(byte[] bytes) {
	// return null;
	// }
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
							+ ((BCConstant) constant).getCPIndex());
		}
		BCConstantUtf8 CONSTANT_Class = (BCConstantUtf8) constant;
		String name = CONSTANT_Class.getLiteral().toString();
		JavaType type = JavaType.getJavaType(name);
		return type;
	}
}
