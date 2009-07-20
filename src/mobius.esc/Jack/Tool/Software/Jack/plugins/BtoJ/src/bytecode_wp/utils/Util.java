/*
 * Created on Feb 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.utils;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import jml2b.IJml2bConfiguration;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionList;

import bytecode_wp.bcclass.BCClass;
import bytecode_wp.bcexpression.BCLocalVariable;
import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bytecode.BCInstruction;
import bytecode_wp.bytecode.branch.BCJumpInstruction;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.modifexpression.ModifiesArray;
import bytecode_wp.modifexpression.ModifiesDOT;
import bytecode_wp.modifexpression.ModifiesExpression;
import bytecode_wp.modifexpression.ModifiesIdent;
import bytecode_wp.modifexpression.ModifiesLocalVariable;
import bytecode_wp.vcg.VCGPath;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class Util {
	public static boolean DUMP = true;
	public final static PrintStream out = System.out;
	/**
	 * updates the instruction - some of the instructions are wrapped in other objects , e.g. -loop starts and ends, and start of exception handlers
	 * @param _bc
	 * @param update
	 */
	public static void update(BCInstruction[] _bc, BCInstruction update) {
		//int positionToUpdateWith = update.getPosition();
		int bcIndexToUpdate = update.getBCIndex();
		// if it is the same object no need to update
		if (_bc[ bcIndexToUpdate ] != update) {
			_bc[ bcIndexToUpdate ] = update;
		}
	}
	
	public static BCInstruction[] setTargets(BCInstruction[] _bc)  {
		for (int i = 0; i < _bc.length; i++) {		
			if (_bc[i] instanceof BCJumpInstruction) {
				BCInstruction _ih = null;
				int offset;
				offset = ((BCJumpInstruction) _bc[i]).getTargetPosition();
				_ih = getBCInstructionAtPosition(_bc, offset);
				((BCJumpInstruction) _bc[i]).setTarget(_ih);
				_ih.addTargeter(_bc[i]);
			}
		}
		return _bc;
	}
	

	/**
	 * @param i
	 * @return the
	 */
	public static BCInstruction getBCInstructionAtPosition(BCInstruction[] _b,
			int offset) {
		for (int i = 0; i < _b.length; i++) {
			if (_b[i].getPosition() == offset) {
				return _b[i];
			}
		}
		return null;
	}
	
	public static void  dump(BCInstruction[] instrs ){
		
		if (instrs == null) {
			return;
		}
		for (int i =0; i < instrs.length; i++) {
			out.println(instrs[i]);
		}
	
	}	
	public static void  dump(InstructionList list ){
		Instruction[] instrs = list.getInstructions();
		if (instrs == null) {
			return;
		}
		for (int i =0; i < instrs.length; i++) {
			out.println(instrs[i]);
		}
	
	}	
	public static void dump(String s) {
		if (DUMP) {
			out.println(s);
		}
	}
	
	public static void   dump(Vector v ) {
		out.println("===============VCGS num" + v.size() + "=====================================" );
		Enumeration en = v.elements();
		VCGPath b;
		while (en.hasMoreElements()) {
			b =(VCGPath)en.nextElement();
			out.println(b.toString());
		}
		out.println(" ===============VCGS=====================================" );
	} 
	
	public static void dumpMethods(BCClass clazz) {
		Iterator c = clazz.getMethodKeys().iterator();
		while (c.hasNext()) { 
			String m = (String)c.next();
			Util.dump(m);
		}
		
	}
	
	public static Formula atState(IJml2bConfiguration config, Formula formula, ModifiesExpression[] modifExpr, int position ) {
		Formula vectorOfFieldToAssume = null;
		Formula wp = (Formula)formula.copy();
		for (int i = 0; i < modifExpr.length; i++) {
            if (modifExpr[i] == null) {
                continue;
            }
            Formula f = (Formula) modifExpr[i].getPostCondition(config, position);

            if (modifExpr[i] instanceof ModifiesLocalVariable) {
                BCLocalVariable lVar = ((ModifiesLocalVariable) modifExpr[i])
                        .getLocalVariable();

                wp = (Formula) wp.atState(position, lVar);

                vectorOfFieldToAssume = Formula.getFormula(
                        vectorOfFieldToAssume, f, Connector.AND);

            } else if (modifExpr[i] instanceof ModifiesDOT) {
                Expression modified = modifExpr[i].getExpressionModifies();
                wp = (Formula) wp.atState(position,modified);

                vectorOfFieldToAssume = Formula.getFormula(
                        vectorOfFieldToAssume, f, Connector.AND);
            } else if (modifExpr[i] instanceof ModifiesIdent) {
                Expression modified = modifExpr[i].getExpressionModifies();
                /*Expression atState =  modified.atState(position);*/
                wp = (Formula) wp.atState(position, modified);
                vectorOfFieldToAssume = Formula.getFormula(
                        vectorOfFieldToAssume, f, Connector.AND);
            } else if (modifExpr[i] instanceof ModifiesArray) {
            	Expression modified = modifExpr[i].getExpressionModifies();
            	/*Expression atState =  modified.atState(position);*/
                wp = (Formula) wp.atState(position, modified);
                vectorOfFieldToAssume = Formula.getFormula(
                        vectorOfFieldToAssume, f, Connector.AND);
            }

        }
		wp = Formula.getFormula( vectorOfFieldToAssume, wp, Connector.IMPLIES );
		return wp;
	}
}
