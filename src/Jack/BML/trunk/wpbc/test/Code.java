/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package test;

import java.util.Enumeration;

import org.apache.bcel.Repository;

import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.ATHROW;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.CodeExceptionGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.GETSTATIC;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InstructionTargeter;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.NEW;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

import bcclass.BCMethod;
import bytecode.BCInstruction;
import bytecode.block.Block;
import bytecode.block.Trace;
import bytecode.branch.BCJumpInstruction;

import sun.rmi.transport.ObjectTable;
import utils.Util;

import TestBC.A;
import TestBC.B;
/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Code {

	public static void main(String[] args) {
		
		
		JavaClass clazz = Repository.lookupClass(args[0]);
		Method[] methods = clazz.getMethods();
		ConstantPoolGen cp = new ConstantPoolGen(clazz.getConstantPool());
		//6
		MethodGen mg = new MethodGen(methods[6], clazz.getClassName(), cp);
		System.out.println("*** method name " + mg.getName() + "***");
		System.out.println("**********************************");
//		testNewArrayIntsruction(mg, cp);
//		testTypeClass();

//		testGETSTATICIntsruction(mg, cp);
//		testINVOKEVIRTUAL(mg, cp);
		testATHROW(mg, cp);
/*		testCpConstantClass( cp);*/
	/*			System.out.println("**********************************");
		testCpConstantString(cp);
		testCpConstantInteger(cp);
		
		*/
		
		//testGETFIELDIntsruction(mg,cp);
		
		//testNewIntsruction(mg, cp);
		//printLVTable( mg, cp);

		//				testCpConstantClass(cp) ;
		//testIndexedInstructions(mg, cp);    
		//printExcTable( mg) ;
		//       			printBlocks1(mg);
		//printLVTable(mg);  
		//				printBlocksOld(mg);

	}
	
	public static void testGETSTATICIntsruction(MethodGen mg, ConstantPoolGen cp) {
			InstructionList il = mg.getInstructionList();
			Instruction[] instrs = il.getInstructions();
			GETSTATIC _getF = null;
			for (int i = 0; i < instrs.length; i++) {
				if (instrs[i] instanceof GETSTATIC
				) {
					_getF = (GETSTATIC) instrs[i];
					System.out.println("instr     " + _getF.toString());
					//System.out.println(" index pointing at   " + _newarr.getIndex());
					break;
				}
			}
		//	Type typeL = _checkcast.getLoadClassType(cp);
			Type type = _getF.getType(cp);
			//
			System.out.println(" type   " + type.getSignature());
		
			Type classType = _getF.getClassType(cp);
			System.out.println("class type      " + classType.getSignature());
			
			int index_cp = _getF.getIndex();
			ConstantFieldref cpConstantField = (ConstantFieldref)cp.getConstant(index_cp);
			ConstantClass cpConstantClass =  (ConstantClass)cp.getConstant(cpConstantField.getClassIndex());
			System.out.println("cp constant class:  " + cpConstantClass.toString());
			
	}
	
	public static void testATHROW(MethodGen mg, ConstantPoolGen cp) {
		InstructionList il = mg.getInstructionList();
		Instruction[] instrs = il.getInstructions();
		ATHROW athrow = null;
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof ATHROW
			) {
				athrow = (ATHROW) instrs[i];
				System.out.println("instr     " + athrow.toString());
				//System.out.println(" index pointing at   " + _newarr.getIndex());
				break;
			}
		}
		Class[] _excThrown = athrow.getExceptions();
		if ( _excThrown == null) {
			System.out.println( " no excepttions thrown");
			return;
		}
		System.out.println( " ***");
		System.out.println( " excepttions thrown : ");
		for (int i = 0; i< _excThrown.length; i++) {
			System.out.println(_excThrown[i].getName());
		}
	}
	
	public static void testINVOKEVIRTUAL(MethodGen mg, ConstantPoolGen cp) {
		InstructionList il = mg.getInstructionList();
		Instruction[] instrs = il.getInstructions();
		INVOKEVIRTUAL invoke = null;
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof INVOKEVIRTUAL
			) {
				invoke = (INVOKEVIRTUAL) instrs[i];
				System.out.println("instr     " + invoke.toString());
				//System.out.println(" index pointing at   " + _newarr.getIndex());
				break;
			}
		}
	//	Type typeL = _checkcast.getLoadClassType(cp);
		Type type = invoke.getType(cp);
		//
		System.out.println(" type   " + type.getSignature());
		
		Type classType = invoke.getClassType(cp);
		System.out.println("class type      " + classType.getSignature());
	
		Class[] _excThrown = invoke.getExceptions();
		if ( _excThrown == null) {
			System.out.println( " no excepttions thrown");
			return;
		}
		System.out.println( " ***");
		System.out.println( " excepttions thrown : ");
		for (int i = 0; i< _excThrown.length; i++) {
			System.out.println(_excThrown[i].getName());
		}
	}
	
	public static void testGETFIELDIntsruction(MethodGen mg, ConstantPoolGen cp) {
		InstructionList il = mg.getInstructionList();
		Instruction[] instrs = il.getInstructions();
		GETFIELD _getF = null;
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof GETFIELD
			) {
				_getF = (GETFIELD) instrs[i];
				System.out.println("instr     " + _getF.toString());
				//System.out.println(" index pointing at   " + _newarr.getIndex());
				break;
			}
		}
	//	Type typeL = _checkcast.getLoadClassType(cp);
		Type type = _getF.getType(cp);
		//
		System.out.println(" type   " + type.getSignature());
		
		Type classType = _getF.getClassType(cp);
		System.out.println("class type      " + classType.getSignature());
		
		int index_cp = _getF.getIndex();
		ConstantFieldref cpConstantField = (ConstantFieldref)cp.getConstant(index_cp);
		ConstantClass cpConstantClass =  (ConstantClass)cp.getConstant(cpConstantField.getClassIndex());
		System.out.println("cp constant class:  " + cpConstantClass.toString());
	}
	
	
	public static void testTypeClass()  {
		Type type = Type.getType("[[[Ljava/lang/String;"); 
		System.out.println("bcel type signature " + type.getSignature());
//		Class _class = Class.forName("java.lang.String[");
		System.out.println(String[][][].class.toString());
		System.out.println(String[][][].class.getName());
	}
	
	
	public static void testNewArrayIntsruction(MethodGen mg, ConstantPoolGen cp) {
		InstructionList il = mg.getInstructionList();
		Instruction[] instrs = il.getInstructions();
		ANEWARRAY _newarr = null;
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof ANEWARRAY
			) {
				_newarr = (ANEWARRAY) instrs[i];
				System.out.println("instr     " + _newarr.toString());
				//System.out.println(" index pointing at   " + _newarr.getIndex());
				break;
			}
		}
	//	Type typeL = _checkcast.getLoadClassType(cp);
		Type type = _newarr.getType(cp);
		//System.out.println("load class type      " + typeL.getSignature());
		System.out.println(" type   " + type.getSignature());
	}


	public static void testcastIntsruction(MethodGen mg, ConstantPoolGen cp) {
		InstructionList il = mg.getInstructionList();
		Instruction[] instrs = il.getInstructions();
		CHECKCAST _checkcast = null;
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof CHECKCAST
			) {

				_checkcast = (CHECKCAST) instrs[i];
				System.out.println("instr     " + _checkcast.toString());
				System.out.println(" index pointing at   " + _checkcast.getIndex());
				break;
			}
		}
	//	Type typeL = _checkcast.getLoadClassType(cp);
		Type type = _checkcast.getType(cp);
		//System.out.println("load class type      " + typeL.getSignature());
		System.out.println(" type   " + type.getSignature());
	}

	public static void testNewIntsruction(MethodGen mg, ConstantPoolGen cp) {
		InstructionList il = mg.getInstructionList();
		Instruction[] instrs = il.getInstructions();
		NEW _new = null;
		for (int i = 0; i < instrs.length; i++) {
			if (instrs[i] instanceof NEW) {

				_new = (NEW) instrs[i];
				System.out.println("instr     " + _new.toString());
				System.out.println(" index pointing at   " + _new.getIndex());
				break;
			}
		}
		Type typeL = _new.getLoadClassType(cp);
		Type type = _new.getType(cp);
		System.out.println("load class type      " + typeL.getSignature());
		System.out.println(" type   " + type.getSignature());
	}

	public static void testCpConstantClass(ConstantPoolGen _cpg) {
		ConstantClass cc = (ConstantClass) _cpg.getConstant(48);
		ConstantPool _cp = _cpg.getConstantPool();
		dump("ConstantClass  getBytes    " + cc.getBytes(_cp));
		dump("ConstantClass  getConstantValue    " + (String) cc.getConstantValue(_cp));
	}
	
	public static void testCpConstantInteger(ConstantPoolGen _cpg) {
		int i = 0;
		for (i = 0; i < _cpg.getSize(); i++) {
			if ( _cpg.getConstant(i) instanceof ConstantInteger) {
				dump(    _cpg.getConstant(i).toString());
				break;
			}
		}
		if (i > _cpg.getSize() ) {
			return;
		} 
		ConstantInteger cc = (ConstantInteger) _cpg.getConstant(i);
		dump(cc.toString());
		ConstantPool _cp = _cpg.getConstantPool();
		//dump("getBytes  of constantstring  " + cc.getBytes(_cp));
		
		dump("constantstring  getConstantValue  " +  ((Integer)cc.getConstantValue(_cp)).intValue() );

	}
	
	
	public static void testCpConstantString(ConstantPoolGen _cpg) {
		int i = 0;
		for (i = 0; i < _cpg.getSize(); i++) {
			if ( _cpg.getConstant(i) instanceof ConstantString) {
				dump(    _cpg.getConstant(i).toString());
				break;
			}
		}
		if (i > _cpg.getSize() ) {
			return;
		} 
		ConstantString cc = (ConstantString) _cpg.getConstant(i);
		dump(cc.toString());
		ConstantPool _cp = _cpg.getConstantPool();
		//dump("getBytes  of constantstring  " + cc.getBytes(_cp));
		dump("constantstring  getConstantValue  " + (Integer) cc.getConstantValue(_cp));
		
	}


	public static void printLVTable(MethodGen mg, ConstantPoolGen cp) {
		LocalVariableGen[] lvs = mg.getLocalVariables();
		LocalVariable _lv;
		for (int i = 0; i < lvs.length; i++) {
			_lv = lvs[i].getLocalVariable(cp);
			dump(
				lvs[i].getName()
					+ "  cp index : "
					+ lvs[i].getIndex()
					+ " | type "
					+ lvs[i].getType().toString()
					+ "| signature "
					+ _lv.getSignature());
		}
	}

	public static void printExcTable(MethodGen mg) {
		CodeExceptionGen[] ehs = mg.getExceptionHandlers();

		for (int i = 0; i < ehs.length; i++) {
			ObjectType _t = (ObjectType) ehs[i].getCatchType();
			if (_t == null) {
				dump(i + " :  " + "any");
			} else {
				dump(i + " :  " + _t.toString());
			}
		}

	}

	//	
	//	public static void printBlocks1(MethodGen mg) {
	//			InstructionList   il    = mg.getInstructionList();
	//			BCInstruction[] _bca = Util. wrapByteCode(il, mg );
	//			Trace trace = new Trace( _bca);
	//			if (trace.getEntryBlocks() != null) {
	//				dump("Entry Block" + trace.getEntryBlocks().size()); 
	//				//trace.dump();
	//			} 
	//	}

	public static void testIndexedInstructions(
		MethodGen mg,
		ConstantPoolGen cp) {
		InstructionList il = mg.getInstructionList();
		InstructionHandle[] _iharr = il.getInstructionHandles();
		for (int i = 0; i < _iharr.length; i++) {
			if (_iharr[i].getPosition() == 36) {
				dump(_iharr[i].toString());
				dump(
					"points to CP index  "
						+ ((INVOKEVIRTUAL) _iharr[i].getInstruction())
							.getIndex());
				ConstantMethodref cm =
					(ConstantMethodref) cp.getConstant(
						((INVOKEVIRTUAL) _iharr[i].getInstruction())
							.getIndex());
				dump(
					"at cp index  "
						+ ((INVOKEVIRTUAL) _iharr[i].getInstruction()).getIndex()
						+ " method const "
						+ cm.toString());
				return;
			}
		}
	}

/*	public static void printBlocks_new_DS(Enumeration blocks) {
		Block b;
		BCJumpInstruction instr;
		Enumeration nexts;
		while (blocks.hasMoreElements()) {
			b = (Block) (blocks.nextElement());
			b.dump("");
			if (b.getLast() instanceof BCJumpInstruction) {
				instr = (BCJumpInstruction) b.getLast();
				if (instr.getTargetBlocks() == null) {
					dump(
						"the instruction for which target is null   "
							+ instr.getInstructionHandle().toString());
				}
				nexts = instr.getTargetBlocks().elements();
				printBlocks_new_DS(nexts);
			}
		}
	}*/

	//	public static void printTrace(MethodGen mg ) {
	//		InstructionList   il    = mg.getInstructionList();
	//		BCInstruction[] _bca = Util. wrapByteCode(il );
	//		Block b = Util.getBlocksStartingAt(_bca[0]);
	//		b.dump("");
	//	}

	/**
	 * @param string
	 */
	private static void dump(String str) {
		if (Util.DUMP) {
			System.out.println(str);
		}
	}

/*	//	//offset ok
		private static void printBytecode( MethodGen mg  ) {
			InstructionList   il    = mg.getInstructionList();
			BCInstruction[] _bca = BCMethod.wrapByteCode(il , mg);
			BCInstruction _i = _bca[0];
			while(_i != null ) {
				System.out.println(_i.getPosition() + " " +_i.getInstructionHandle().toString());
				if ((_i instanceof BCJumpInstruction) && (((BCJumpInstruction)_i).getTarget() != null)) {
					Instruction ins = ( (BCJumpInstruction)_i).getTarget().getInstructionHandle().getInstruction();
					int offset = ( (BCJumpInstruction)_i).getTarget().getPosition();
					System.out.println("|");
					System.out.println("| -> target " + offset +"   "+ ins.toString());
				//System.out.println("| -> target " + ((BranchInstruction)( (BCJumpInstruction)_i).getInstructionHandle()).get );
				}
				_i = _i.getNext();
			}
		}*/

	/**
	 * @param mg
	 */
	private static void printCode(MethodGen mg) {
		InstructionList il = mg.getInstructionList();
		//		InstructionHandle[] ih = il.getInstructionHandles();
		//		InstructionHandle h;
		//		InstructionTargeter[] it;
		//		for (int i =0; i < ih.length; i++ ){
		//			h = ih[i];
		//			System.out.println(ih[i].toString());
		//			
		//			if ((it = ih[i].getTargeters()) == null ) {
		//				System.out.println("no targeters" );	
		//			} else { 
		//				System.out.println(" there are targeters" );
		//				for (int s = 0; s < it.length; s++) {
		//					System.out.println(" targeter : " + it[s].toString() );
		//				}
		//			} 
		//			System.out.println("===============================" );
		//		}

		InstructionHandle ih = il.getStart();

		InstructionTargeter[] it;
		while (ih != null) {

			//					System.out.println(ih.toString() );
			System.out.println(" positiion    " + ih.getPosition());
			System.out.println(
				" length       " + ih.getInstruction().getLength());
			//					if ((it = ih.getTargeters()) == null ) {
			//						System.out.println("no targeters" );	
			//					} else { 
			//						System.out.println(" there are targeters" );
			//						for (int s = 0; s < it.length; s++) {
			//							System.out.println(" targeter : " + it[s].toString() );
			//						}
			//					} 
			System.out.println("===============================");
			ih = ih.getNext();
		}

	}
}