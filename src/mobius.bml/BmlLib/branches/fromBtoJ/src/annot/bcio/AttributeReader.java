package annot.bcio;

import java.io.ByteArrayInputStream;
import java.io.DataInputStream;
import java.io.IOException;

import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Unknown;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.attributes.Assert;
import annot.bcclass.attributes.AssertTable;
import annot.bcclass.attributes.BCAttribute;
import annot.bcclass.attributes.Exsures;
import annot.bcclass.attributes.ExsuresTable;
import annot.bcclass.attributes.LoopSpecification;
import annot.bcclass.attributes.MethodSpecification;
import annot.bcclass.attributes.ModifiesSet;
import annot.bcclass.attributes.Postcondition;
import annot.bcclass.attributes.SecondConstantPool;
import annot.bcclass.attributes.SingleLoopSpecification;
import annot.bcclass.attributes.SpecificationCase;
import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.ArrayAccessExpression;
import annot.bcexpression.BCLocalVariable;
import annot.bcexpression.CastExpression;
import annot.bcexpression.ConditionalExpression;
import annot.bcexpression.Expression;
import annot.bcexpression.ExpressionConstants;
import annot.bcexpression.FieldAccess;
import annot.bcexpression.MethodInvocation;
import annot.bcexpression.NULL;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.Variable;
import annot.bcexpression.javatype.JavaObjectType;
import annot.bcexpression.javatype.JavaType;
import annot.bcexpression.jml.ELEMTYPE;
import annot.bcexpression.jml.JML_CONST_TYPE;
import annot.bcexpression.jml.OLD;
import annot.bcexpression.jml.RESULT;
import annot.bcexpression.jml.TYPEOF;
import annot.bcexpression.jml._TYPE;
import annot.constants.ArrayLengthConstant;
import annot.constants.BCConstant;
import annot.constants.BCConstantFieldRef;
import annot.constants.BCConstantMethodRef;
import annot.constants.BCConstantUtf8;
import annot.formula.Connector;
import annot.formula.Formula;
import annot.formula.Predicate0Ar;
import annot.formula.Predicate2Ar;
import annot.formula.PredicateSymbol;
import annot.formula.Quantificator;
import annot.formula.QuantifiedFormula;
import annot.formula.UnknownFormula;
import annot.modifexpression.AllArrayElem;
import annot.modifexpression.ArrayElemFromTo;
import annot.modifexpression.Everything;
import annot.modifexpression.ModifiesArray;
import annot.modifexpression.ModifiesDOT;
import annot.modifexpression.ModifiesExpression;
import annot.modifexpression.ModifiesIdent;
import annot.modifexpression.ModifiesLocalVariable;
import annot.modifexpression.Nothing;
import annot.modifexpression.SingleIndex;
import annot.modifexpression.SpecArray;
import annot.modifexpression.UnknownArray;
import annot.modifexpression.UnknownModifies;
import annot.vm.Counter;
import annot.vm.Stack;

public class AttributeReader {
	private static int pos;
	private static BCClass clazz;
	private static BCLocalVariable[] localVariables;
	public static int bytes_read = 1;
	public static int bytes_total = 1;
	public static boolean ok;
	public static final int ERROR_READING_OUT_OF_ARR = -1;
	public static boolean silent = false;

	public static void syso(String str) {
		if (!silent)
			System.out.println(str);
	}
	
	public static BCAttribute readAttribute(Unknown privateAttr,
			BCClass _clazz, BCLocalVariable[] _localVariables,
			BCMethod method) throws ReadAttributeException {
		int alen = privateAttr.getLength();
		ok = true;
		bytes_total += alen;
		clazz = _clazz;
		/* constantPool = _clazz.getConstantPool(); */
		localVariables = _localVariables;
		String name = privateAttr.getName();
		if (name.equals(BCAttribute.ASSERT)) {
			return readAssertTable(privateAttr.getBytes(), method);
		}
		if (name.equals(BCAttribute.SET))
			try {
				throw new Exception("SET attribute found!");
			} catch (Exception e) {
				e.printStackTrace();
			}
//		if (name.equals(BCAttribute.SET)) {
//			return readSetTable(privateAttr.getBytes());
//		}
		if (name.equals(BCAttribute.MethodSpecification)) {
			return readMethodSpecification(privateAttr.getBytes());
		}
		if (name.equals(BCAttribute.LOOPSPECIFICATION)) {
			return readLoopSpecification(privateAttr.getBytes(), method);
		}
//		if (name.equals(BCAttribute.BLOCKSPECIFICATION)) {
//			return readBlockSpecification(privateAttr.getBytes());
//		}
//		if (name.equals(BCAttribute.HISTORY_CONSTRAINTS)) {
//			return readHistoryConstraints(privateAttr.getBytes());
//		}
//		if (name.equals(BCAttribute.CLASSINVARIANT)) {
//			return readClassInvariant(privateAttr.getBytes());
//		}
		if (name.equals(BCAttribute.SECOND_CONSTANT_POOL)) {
			return readSecondConstantPool(privateAttr.getBytes());
		}
		syso("Unknown attribute: " + name + ", skipping " + alen + " bytes.");
		return null;
	}

//	// /////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//	// ////////////////////////////////////Class
//	// Specification/////////////////////////////////////////////
//	// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//	private static HistoryConstraints readHistoryConstraints(byte[] bytes)
//			throws ReadAttributeException {
//		// here the length of the attribute not needed
//		pos = 0;
//		Formula predicate = (Formula) readExpression(bytes);
//		HistoryConstraints historyConstraints = new HistoryConstraints(
//				predicate);
//		return historyConstraints;
//	}
//
//	private static ClassInvariant readClassInvariant(byte[] bytes)
//			throws ReadAttributeException {
//		// here the length of the attribute not needed
//		pos = 0;
//		Formula predicate = (Formula) readExpression(bytes);
//		ClassInvariant classInvariant = new ClassInvariant(predicate, JavaType
//				.getJavaType(clazz.getName()), ClassInvariant.INSTANCE);
//		return classInvariant;
//	}
//	
	private static SecondConstantPool readSecondConstantPool(byte[] bytes) throws ReadAttributeException {
		try {
			bytes_read += bytes.length; // XXX unchecked
			syso("Reading second constant pool...");
			SecondConstantPool scp = new SecondConstantPool(new DataInputStream(new ByteArrayInputStream(bytes)));
			syso("...done");
			return scp;
		} catch (IOException e) {
			System.err.println("error in reading cp2");
			return null;
		}
	}
//
//	// ////////////////////////////////////////end Class
//	// specification//////////////////////////////////////
//
//	// //////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//	// ////////////////////////////////////Method
//	// Specification/////////////////////////////////////////////
//	// ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//	// //////////////////// start : block specification
//	// /////////////////////////////////////////////////
//	private static BlockSpecification readBlockSpecification(byte[] bytes)
//			throws ReadAttributeException {
//		pos = 0;
//		int attribute_length = bytes.length;
//		int attributes_count = readAttributeCount(bytes);
//		if (attribute_length == 2) {
//			return null;
//		}
//		if (attributes_count <= 0) {
//			throw new ReadAttributeException(
//					"a wrong BlockSpecification attribute : attribute count  = "
//							+ attributes_count + " and attribute length =  "
//							+ attribute_length);
//		}
//		SingleBlockSpecification[] blockSpecs = new SingleBlockSpecification[attributes_count];
//		for (int i = 0; i < attributes_count; i++) {
//			blockSpecs[i] = readSingleBlockSpecification(bytes);
//		}
//		BlockSpecification blockSpec = new BlockSpecification(blockSpecs);
//		return blockSpec;
//	}
//
//	/**
//	 * @param bytes
//	 * @return
//	 */
//	private static SingleBlockSpecification readSingleBlockSpecification(
//			byte[] bytes) throws ReadAttributeException {
//		int startCpInd = readShort(bytes);
//		int endCpInd = readShort(bytes);
//		Formula precondition = (Formula) readExpression(bytes);
//		int modifiesCount = readShort(bytes);
//		Expression[] modifies = null;
//		if (modifiesCount > 0) {
//			modifies = new Expression[modifiesCount];
//			for (int i = 0; i < modifiesCount; i++) {
//				modifies[i] = readExpression(bytes);
//			}
//		}
//		Formula postcondition = (Formula) readExpression(bytes);
//		SingleBlockSpecification blockSpec = new SingleBlockSpecification(
//				startCpInd, endCpInd, precondition, modifies, postcondition);
//		return blockSpec;
//	}
//
//	// //////////////////// end : block specification
//	// /////////////////////////////////////////////////

	// //////////////////// start : loopspecifcation
	// /////////////////////////////////////////////////

	private static LoopSpecification readLoopSpecification(byte[] bytes, BCMethod method)
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
		syso("  loops specification:");
		printByteArr(bytes); // syso -- wywali
		SingleLoopSpecification[] loopSpecs = new SingleLoopSpecification[attributes_count];
		for (int i = 0; i < attributes_count; i++) {
			if (pos >= attribute_length) {
				throw new ReadAttributeException(
						"uncorrect LoopSpecification  attribute attribute_length "
								+ attribute_length
								+ " <  actual length of attribute ");
			}
			loopSpecs[i] = readSingleLoopSpecification(bytes, method);
		}
		LoopSpecification loopSpe = new LoopSpecification(loopSpecs);
		syso("  read " + pos + " of " + bytes.length + " bytes " +
				((pos == bytes.length) ? "(ok)" : "(err)"));
		return loopSpe;
	}

	private static SingleLoopSpecification readSingleLoopSpecification(
			byte[] bytes, BCMethod method) throws ReadAttributeException {
		int loopIndex = readShort(bytes);
		syso("    modifies");
		ModifiesSet modifies = readModifies(bytes);
		syso("    invariant");
		Expression invariant = readExpression(bytes);
		syso("    decreases");
		Expression decreases = readExpression(bytes);
		SingleLoopSpecification loopSpec = new SingleLoopSpecification(
				loopIndex, modifies, (Formula) invariant, decreases, method);
		return loopSpec;
	}

	// //////////////////// end : loopspecifcation
	// /////////////////////////////////////////////////

//	// ////////////////////// start : set
//	// table/////////////////////////////////////////////////
//
//	/**
//	 * the method reads an array of set model statements. In Jml this statements
//	 * are of the form: set a = expr where a is a ghost variable
//	 */
//	private static SETTable readSetTable(byte[] bytes)
//			throws ReadAttributeException {
//		pos = 0;
//		int attribute_length = bytes.length;
//		int attributes_count = readAttributeCount(bytes);
//		if (attribute_length <= 0) {
//			return null;
//		}
//		if (attributes_count == 0) {
//			return null;
//		}
//		SET[] sets = new SET[attributes_count];
//		for (int i = 0; i < attributes_count; i++) {
//			if (pos >= attribute_length) {
//				throw new ReadAttributeException(
//						"uncorrect Assert  attribute attribute_length "
//								+ attribute_length
//								+ " <  actual length of attribute ");
//			}
//			sets[i] = readSet(bytes);
//		}
//		SETTable setTable = new SETTable(sets);
//		return setTable;
//	}
//
//	/**
//	 * @param pos -
//	 *            the position from which starts the assert object
//	 * @param bytes
//	 *            -the array from which the assert object is read
//	 * @param assert -
//	 *            an object that should be initialised by the method
//	 * @return an object of type <code>bcclass.attributes.SET</code>
//	 */
//	private static SET readSet(byte[] bytes) throws ReadAttributeException {
//		int pcIndex = readShort(bytes);
//		Expression jmlExprToAssign = readExpression(bytes);
//		Expression exprAssign = readExpression(bytes);
//		return new SET(pcIndex, jmlExprToAssign, exprAssign);
//	}
//
//	// /////////////////////end : set table
//	// /////////////////////////////////////////////////

	// //////////////////// start : assert table
	// /////////////////////////////////////////////////
	private static AssertTable readAssertTable(byte[] bytes, BCMethod method)
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
			asserts[i] = readAssert(bytes, method);
		}
		AssertTable assertTable = new AssertTable(asserts);
		return assertTable;
	}

	/**
	 * @param pos -
	 *            the position from which starts the assert object
	 * @param bytes
	 *            -the array from which the assert object is read
	 * @param method - current method
	 * @param assert -
	 *            an object that should be initialised by the method
	 * @return the leftmost index into the byte array bytes that is not read by
	 *         the method
	 */
	private static Assert readAssert(byte[] bytes, BCMethod method)
			throws ReadAttributeException {
		int pcIndex = readShort(bytes);
		Formula formula = (Formula) readExpression(bytes);
		return new Assert(formula, pcIndex, method);
	}

	// //////////////////// end : assert table
	// /////////////////////////////////////////////////

//	// //////////////// start : method specification
//	// /////////////////////////////////////////////////
//
////use undetermined...	
////	private static MethodInvocation readMethodInvocation(byte[] bytes)
////			throws ReadAttributeException {
////		return null;
////	}

	private static String printByte(int x) {
		int b = (x + 256) % 256;
		return Integer.toHexString(b);
	}
	
	private static void printByteArr(byte[] bytes) {
		if (silent)
			return;
		System.out.print("  ");
		for (int i=0; i<bytes.length; i++) {
			System.out.print(printByte(bytes[i]) + " ");
		}
		System.out.println();
	}
	
	private static MethodSpecification readMethodSpecification(byte[] bytes)
			throws ReadAttributeException {
		pos = 0;
		int attribute_length = bytes.length;
		syso("  method specification:");
		printByteArr(bytes); // syso -- wywali
		syso("    precondition");
		Formula precondition = (Formula) readExpression(bytes);
		int attributes_count = readAttributeCount(bytes);
		if (attribute_length <= 0) { // XXX po co?
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
//		SpecificationCase[] specCases = null; // wywali
		MethodSpecification methodSpec = new MethodSpecification(precondition,
				specCases);
		syso("  read " + pos + " of " + bytes.length + " bytes " +
				((pos == bytes.length) ? "(ok)" : "(err)"));
		return methodSpec;
	}

	private static SpecificationCase readSpecificationCase(byte[] bytes)
			throws ReadAttributeException {
		syso("    specCase");
		Formula precondition = (Formula) readExpression(bytes);
		syso("      modifies");
		ModifiesSet modifies = readModifies(bytes);
		syso("      postcondition");
		Formula postcondition = (Formula) readExpression(bytes);
		syso("      exsures");
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
		// TODO odkomentowa reszt konstruktora ModifyExpression
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
		syso("Unknown nodify expression");
		return new UnknownModifies();
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
		syso("Unknown spec arr");
		return new UnknownArray();
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

//	// ////////////////// end : method specification
//	// /////////////////////////////////////////////////
//
//	// //////////////////////////////////////////////////////////////////////////////////////////////////////////////
//	// ////////////////////////////////Expressions and Formulas
//	// ///////////////////////////////////////////////////////////////
//	// /////////////////////////////////////////////////////////////////////////////////////////////////////////////
//// jgc: use undetermined...
////	private static int readAttributeLength(byte[] bytes) {
////		int attribute_length = readInt(bytes);
////		return attribute_length;
////	}

	private static int readAttributeCount(byte[] bytes) {
		if (!ok) {
			syso("        skipping attributes");
			return 0;
		}
		int attribute_count = readShort(bytes);
		return attribute_count;
	}

	private static int readInt(byte[] bytes) {
		int integer = ((bytes[pos] & 0xff) << 24)
				| ((bytes[pos + 1] & 0xff) << 16)
				| ((bytes[pos + 2] & 0xff) << 8) | (bytes[pos + 3] & 0xff);
		pos = pos + 4;
		bytes_read += 4;
		return integer;
	}

	private static int readShort(byte[] bytes) {
		int _short = ((bytes[pos] & 0xff) << 8) | (bytes[pos + 1] & 0xff);
		pos = pos + 2;
		bytes_read += 2;
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
		bytes_read++;
		return _byte;
	}

///*	*//**
//	 * @param bytes - byte array containing the encoding of a user defined class
//	 * 	attribute 
//	 * @param p - 
//	 * @return  the value in the array byted at position pos
//	 *//*
//	private static int checkByteValue(byte[] bytes, int p) {
//		int _byte = bytes[p] & 0xff;
//		return _byte;
//	}*/
//
	private static Expression readExpression(byte[] bytes)
			throws ReadAttributeException {
		if (!ok)
			return new UnknownFormula("...");
		int _byte = readByte(bytes);
//		System.out.print(printByte(_byte) + ":");
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
			Expression e = new ArithmeticExpression(e1,	ExpressionConstants.NEG);
			return e;
		} else if (_byte == Code.BITWISEAND) { // Bitwise
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = new ArithmeticExpression(e1, e2,
					ExpressionConstants.BITWISEAND);
			return e;
		} else if (_byte == Code.BITWISEOR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = new ArithmeticExpression(e1, e2,
					ExpressionConstants.BITWISEOR);
			return e;
		} else if (_byte == Code.BITWISEXOR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e = new ArithmeticExpression(e1, e2,
					ExpressionConstants.BITWISEXOR);
			return e;
		} else if (_byte == Code.SHL) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
			// e1 the expression that is shifted
			// e2 is the number of positions e1 to shift with
			new ArithmeticExpression(e1, e2, ExpressionConstants.SHL);
			return e;
		} else if (_byte == Code.SHR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
			// e1 the expression that is shifted
			// e2 is the number of positions e1 to shift with
			new ArithmeticExpression(e1, e2, ExpressionConstants.SHR);
			return e;
		} else if (_byte == Code.USHR) {
			Expression e1 = readExpression(bytes);
			Expression e2 = readExpression(bytes);
			Expression e =
			// e1 the expression that is shifted
			// e2 is the number of positions e1 to shift with
			new ArithmeticExpression(e1, e2, ExpressionConstants.USHR);
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
		} else if (_byte == Code._type) {
			JavaType javaType = readJavaType(bytes);
			Expression _type = new _TYPE(javaType);
			return _type;
		} else if (_byte == Code.TYPE) {
			Expression TYPE = JML_CONST_TYPE.JML_CONST_TYPE;
			return TYPE;
		} else if (_byte == Code.ARRAY_ACCESS) {
			Expression array = readExpression(bytes);
			Expression arrIndex = readExpression(bytes);
			if (array instanceof OLD) { //XXX ??
				syso("Unchecked: old array");
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
		} else if (_byte == Code.FULL_QUALIFIED_NAME) {// .
			Expression expr = readExpression(bytes);
			Expression constant = readExpression(bytes);
			if (constant instanceof OLD) {// XXX ??
				syso("Unchecked: old constant");
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
			if (localVariables.length <= ind) {		// TODO add ghost field case
				syso("        ERROR: lvar index ("+ind+") out of bounds ("+localVariables.length+") or ghost field");
				Formula f = new UnknownFormula("lvar index out of bounds!");
				ok = true;
				return f;
//				throw new ArrayIndexOutOfBoundsException();
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
			BCConstant constantField = clazz.getConstantPool().getConstant(cpIndex);
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
//			Formula formula = Formula.getFormula(f1, f2, Connector.AND);
			return new Formula(f1, f2, Connector.AND);
		} else if (_byte == Code.OR) {
			Expression f1 = readExpression(bytes);
			Expression f2 = readExpression(bytes);
//			Formula formula = Formula.getFormula(f1, f2, Connector.OR);
			return new Formula(f1, f2, Connector.OR);
		} else if (_byte == Code.IMPLIES) {
			Expression f1 = readExpression(bytes);
			Expression f2 = readExpression(bytes);
//			Formula formula = Formula.getFormula(f1, f2, Connector.IMPLIES);
			return new Formula(f1, f2, Connector.IMPLIES);
		} else if (_byte == Code.NOT) {
			Expression f1 = readExpression(bytes);
			return new Formula(f1, Connector.NOT);
//			if (f1 instanceof Formula) {
//				Formula formula = Formula.getFormula((Formula) f1,
//						Connector.NOT);
//				return formula;
//			}
//			DesugarNegBoolExpr des = new DesugarNegBoolExpr(f1, true);
//			return des;
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
			Expression expr2 = readExpression(bytes);
			return new Predicate2Ar(expr1, expr2, PredicateSymbol.EQ);
		} else if (_byte == Code.NOTEQ) {
			Expression expr1 = readExpression(bytes);
			Expression expr2 = readExpression(bytes);
			return new Predicate2Ar(expr1, expr2, PredicateSymbol.NOTEQ);
//			Formula predicate = Formula.getFormula(Predicate2Ar.getPredicate(
//					expr1, expr2, PredicateSymbol.EQ), Connector.NOT);
//			return predicate;
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

		} if (_byte == Code.EXISTS) {
			int numBoundVars = readByte(bytes);
			Variable[] vars = new Variable[numBoundVars];
			for (int i = 0; i < numBoundVars; i++) {
				JavaType jType = readJavaType(bytes);
				Variable var = new Variable(i, jType);
				vars[i] = var;
			}
			Quantificator exists = new Quantificator(Quantificator.EXISTS, vars);
			Formula f = (Formula) readExpression(bytes);
//			Formula forallFormula = Formula.getFormula(f, exists);
			return new QuantifiedFormula(f, exists);
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
//			Formula forallFormula = Formula.getFormula(f, forall);
			return new QuantifiedFormula(f, forall);
		}
		syso("ERROR: Unknown Code - " + printByte(_byte));
		return new UnknownFormula("0x"+printByte(_byte));
	}
//
//	/*	*//**
//			 * reads the encoding of a cp constant
//			 * 
//			 * @param bytes
//			 * @return
//			 */
//	/*
//	 * private static final BCConstant readConstant(byte[] bytes) throws
//	 * ReadAttributeException { int _byte = readByte(bytes); if (_byte ==
//	 * Code.ARRAYLENGTH) { ArrayLengthConstant length = new
//	 * ArrayLengthConstant(); return length; } else if (_byte == Code.FIELD_REF) { //
//	 * read the index of the field_ref in the constant pool // int cpIndex =
//	 * readShort(bytes); int cpIndex = readShort(bytes); // find the object in
//	 * the constant field BCConstant constantField =
//	 * constantPool.getConstant(cpIndex); if (!(constantField instanceof
//	 * BCConstantFieldRef)) { throw new ReadAttributeException( "Error reading
//	 * in the Constant Pool : reason : CONSTANT_Fieldref expected at index " +
//	 * cpIndex); } return constantField; } else if (_byte ==
//	 * Code.JML_MODEL_FIELD) { // int cpIndex = readShort(bytes); int cpIndex =
//	 * readShort(bytes); BCConstant constantField =
//	 * constantPool.getConstant(cpIndex); if (!(constantField instanceof
//	 * BCConstantFieldRef)) { throw new ReadAttributeException( "Error reading
//	 * in the Constant Pool :reason : CONSTANT_Fieldref expected for a model
//	 * field ref at index " + cpIndex); } return constantField; } else if (_byte ==
//	 * Code.METHOD_REF) { int cpIndex = readShort(bytes); BCConstant
//	 * consantMethodRef = constantPool.getConstant(cpIndex); if
//	 * (!(consantMethodRef instanceof BCConstantMethodRef)) { throw new
//	 * ReadAttributeException( "Error reading in the Constant Pool : reason:
//	 * CONSTANT_Methodref expected at index " + cpIndex); } return
//	 * consantMethodRef; } else if (_byte == Code.JAVA_TYPE) { int cpIndex =
//	 * readShort(bytes); BCConstant constantUtf8 =
//	 * constantPool.getConstant(cpIndex); if (!(constantUtf8 instanceof
//	 * BCConstantUtf8)) { throw new ReadAttributeException( "Error reading in
//	 * the Constant Pool : reason: CONSTANT_Utf8 expected at index " + cpIndex); }
//	 * return constantUtf8; } // may be there should be translation for strings
//	 * return null; }
//	 */
//
//	// private static final Expression readJavaExpression(byte[] bytes) {
//	// return null;
//	// }
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
