/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package test;

import java.util.Enumeration;
import java.util.Vector;

import org.apache.bcel.Repository;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.CodeExceptionGen;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.InstructionTargeter;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.ObjectType;

import bytecode.BCInstruction;
import bytecode.BCJumpInstruction;
import bytecode.Block;
import bytecode.Trace;


import sun.rmi.transport.ObjectTable;
import utils.Util;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Code {
	
	
	public static void main( String[] args ) {
				 JavaClass       clazz   = Repository.lookupClass(args[0]);
				 Method[]        methods = clazz.getMethods();
				 ConstantPoolGen cp      = new ConstantPoolGen(clazz.getConstantPool());
				 //6
				 MethodGen mg       = new MethodGen(methods[6], clazz.getClassName(), cp);
			    System.out.println("*** method name " + mg.getName() + "***");
			    System.out.println("**********************************");
				
//				testCpConstantClass(cp) ;
				//testIndexedInstructions(mg, cp);
			    
			    //printExcTable( mg) ;
       			printBlocks1(mg);
       			//printLVTable(mg);  
//				printBlocksOld(mg);

								
	}
	
	public static void testCpConstantClass(ConstantPoolGen _cpg ) {
		ConstantClass cc = (ConstantClass)_cpg.getConstant(36);
		ConstantPool _cp = _cpg.getConstantPool();
		dump("getBytes    " + cc.getBytes(_cp));
		dump("getConstantValue" + (String)cc.getConstantValue(_cp));
	}
	
	public static void printLVTable(MethodGen mg)  {
		LocalVariableGen[] lvs = mg.getLocalVariables();
		for (int i = 0 ; i < lvs.length; i++) {
			dump(lvs[i].getName() + " at index : " + lvs[i].getIndex() + " has type " + lvs[i].getType().toString());
		}
	}
	
	public static void printExcTable(MethodGen mg) {
		CodeExceptionGen[] ehs = mg.getExceptionHandlers();
		
		for (int i = 0 ; i < ehs.length; i++) {
			ObjectType _t = (ObjectType)ehs[i].getCatchType();
			if (_t == null ) {
				dump(i + " :  " +  "any");
			}else {
				dump(i + " :  " + _t.toString());
			}
		}
			
	}
	 	
	
	public static void printBlocks1(MethodGen mg) {
			InstructionList   il    = mg.getInstructionList();
			BCInstruction[] _bca = Util. wrapByteCode(il, mg );
			Trace trace = new Trace( _bca);
			if (trace.getEntryBlocks() != null) {
				dump("Entry Block" + trace.getEntryBlocks().size()); 
				//trace.dump();
			} 
	}
	
	public static void testIndexedInstructions(MethodGen mg, ConstantPoolGen cp) {
		InstructionList   il    = mg.getInstructionList();
		InstructionHandle[] _iharr =  il.getInstructionHandles(); 
		for (int i = 0 ; i < _iharr.length; i++) {
			if (_iharr[i].getPosition() == 36)  {
				dump(_iharr[i].toString() );
				dump("points to CP index  " +((INVOKEVIRTUAL)_iharr[i].getInstruction()).getIndex());
				ConstantMethodref cm= (ConstantMethodref)cp.getConstant( ((INVOKEVIRTUAL)_iharr[i].getInstruction() ).getIndex() );
				dump("at cp index  " +((INVOKEVIRTUAL)_iharr[i].getInstruction()).getIndex() +" method const " + cm.toString());
				return;
			}
		}
	}
	
	
	public static void printBlocks_new_DS(Enumeration blocks)  {
			Block b;
			BCJumpInstruction instr;
			Enumeration nexts;
			while (blocks.hasMoreElements()) {
					b = (Block)(blocks.nextElement());
					b.dump("");
					if (b.getLast() instanceof BCJumpInstruction) {
						instr = (BCJumpInstruction)b.getLast();
						if (instr.getTargetBlocks() == null) {
							dump("the instruction for which target is null   " + instr.getInstructionHandle().toString());
						}
						nexts = instr.getTargetBlocks().elements(); 
						printBlocks_new_DS(nexts);
					}
					
			}
		
	} 	
	
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

	//offset ok
	private static void printBytecode( MethodGen mg  ) {
		InstructionList   il    = mg.getInstructionList();
		BCInstruction[] _bca = Util. wrapByteCode(il , mg);
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
	}

	/**
	 * @param mg
	 */
	private static void printCode(MethodGen mg) {
		InstructionList   il    = mg.getInstructionList();
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
				while (ih != null ) {
					
//					System.out.println(ih.toString() );
					System.out.println( " positiion    " + ih.getPosition() );
					System.out.println( " length       " + ih.getInstruction().getLength() );
//					if ((it = ih.getTargeters()) == null ) {
//						System.out.println("no targeters" );	
//					} else { 
//						System.out.println(" there are targeters" );
//						for (int s = 0; s < it.length; s++) {
//							System.out.println(" targeter : " + it[s].toString() );
//						}
//					} 
					System.out.println("===============================" );
					ih = ih.getNext();
				}

	}
}