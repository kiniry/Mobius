package annot.bcclass;

import java.util.Iterator;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.LocalVariableGen;
import org.apache.bcel.generic.MethodGen;

import annot.attributes.AType;
import annot.attributes.BCAttributeMap;
import annot.attributes.InCodeAttribute;
import annot.attributes.MethodSpecification;
import annot.bcexpression.BCLocalVariable;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Parsing;

/**
 * This class represents a bytecode method.
 * 
 * @author tomekb
 */
public class BCMethod {

	/**
	 * A flag to choose how bytecode should be displayed.
	 */
	private final static boolean displayStyle = false;

	/**
	 * BCClass containing this method.
	 */
	private BCClass bcc;

	/**
	 * Original (BCEL) method. Do not use any other methodGen's
	 * 		to manipulate bytecode.
	 */
	private MethodGen bcelMethod;

	/**
	 * Method specification attribute.
	 */
	private MethodSpecification mspec;

	/**
	 * Collection of all attributes inside method body.
	 */
	private BCAttributeMap amap;

	/**
	 * Local variable array.
	 */
	private BCLocalVariable[] lvars;
	
	/**
	 * Old local variable array.
	 */
	private BCLocalVariable[] oldvars;

	/**
	 * A standard constructor from BCClass and MethodGen.
	 * 
	 * @param bcc - BCClass containig this method,
	 * @param m - BCEL's methodGen for this method.
	 * @throws ReadAttributeException - if any of BML
	 * 		attributes wasn't correctly parsed
	 * 		by this library.
	 */
	public BCMethod(BCClass bcc, MethodGen m) throws ReadAttributeException {
		MLog.putMsg(MLog.PInfo, "  initializing method: " + m.getName());
		this.bcc = bcc;
		this.bcelMethod = m;
		this.amap = new BCAttributeMap(this);
		LocalVariableGen[] lvgens = m.getLocalVariables();
		int cnt = lvgens.length;
		lvars = new BCLocalVariable[cnt];
		oldvars = new BCLocalVariable[cnt];
		for (int i=0; i<cnt; i++) {
			String name = lvgens[i].getName();
			lvars[i] = new BCLocalVariable(false, this, i, name, lvgens[i]);
			oldvars[i] = new BCLocalVariable(true, this, i, name, lvgens[i]);
		}
		Attribute[] attrs = m.getAttributes();
		AttributeReader ar = new AttributeReader(this);
		for (int i = 0; i < attrs.length; i++) {
			if (attrs[i] instanceof Unknown)
				ar.readAttribute((Unknown) attrs[i]);
		}
	}

	/**
	 * @return String representation of method's header.
	 */
	@Override
	public String toString() {
		return bcelMethod.toString() + "\n";
	}

	/**
	 * Displays method's bytecode with BML annotations.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of method's bytecode.
	 */
	public String printCode(BMLConfig conf) {
		String code = "";
		if (mspec != null)
			code += mspec.printCode(conf);
		code += toString();
		String bcode = "";
		if (displayStyle) {
			InstructionList il = bcelMethod.getInstructionList();
			il.setPositions();
			Iterator iter = bcelMethod.getInstructionList().iterator();
			while (iter.hasNext()) {
				InstructionHandle ih = (InstructionHandle) iter.next();
				bcode += amap.getAllAt(ih).printCode(conf);
				bcode += ih.getPosition()
						+ ": "
						+ ih.getInstruction().toString(
								bcc.getJc().getConstantPool()) + "\n";
			}
		} else {
			bcode += bcelMethod.getMethod().getCode().toString();
			bcode = bcode.substring(bcode.indexOf("\n") + 1);
			bcode = bcode.split("\n\n")[0];
			String[] lines_in = bcode.split("\n");
			bcode = "";
			for (int l = 0; l < lines_in.length; l++) {
				String line = lines_in[l];
				int pc = Integer.parseInt(line.substring(0, line.indexOf(":")));
				String annotLines = "";
				InCodeAttribute[] attrs = amap.getAllAt(findAtPC(pc)).getAll(
						AType.C_ALL);
				for (int i = 0; i < attrs.length; i++)
					annotLines += attrs[i].printCode(conf);
				bcode += Parsing.addComment(annotLines) + line + "\n";
			}
		}
		return code + bcode;
	}

	/**
	 * Adds an annotation to the BCMethod.
	 * 
	 * @param ica - annotation to be added.
	 */
	public void addAttribute(InCodeAttribute ica) {
		MLog.putMsg(MLog.PProgress, "adding attribute: " + ica.toString());
		amap.addAttribute(ica, ica.getMinor());
	}

	/**
	 * Updates BCEL MethodGen's attributes and generates
	 * BCEL's method.
	 * 
	 * @return generated BCEL Method.
	 */
	public Method save() {
		MLog.putMsg(MLog.PInfo, "  saving method: " + bcelMethod.getName());
		AttributeWriter aw = new AttributeWriter(this);
		Attribute[] attrs = BCClass.removeBMLAttributes(bcelMethod
				.getAttributes());
		if (mspec != null)
			attrs = BCClass.addAttribute(attrs, aw.writeAttribute(mspec));
		if (amap.getLength() > 0) {
			attrs = BCClass.addAttribute(attrs, aw.writeAttribute(amap.getAtab()));
			attrs = BCClass.addAttribute(attrs, aw.writeAttribute(amap.getLstab()));
		}
		bcelMethod.removeAttributes();
		for (int i = 0; i < attrs.length; i++)
			bcelMethod.addAttribute(attrs[i]);
		bcelMethod.update();
		bcelMethod.setMaxStack();
		bcelMethod.setMaxLocals();
		return bcelMethod.getMethod();
	}

	/**
	 * @return BCEL MethodGen's instructionList.
	 */
	public InstructionList getInstructions() {
		return bcelMethod.getInstructionList();
	}

	/**
	 * Computes pc numbers for each bytecode instruction of
	 * a method containing this annotation and returns,
	 * and returns pc number of instruction this annotation
	 * is attached to.
	 * 
	 * @return pc number of this annotation's
	 * 		bytecode instruction.
	 */
	public int getPC(InstructionHandle ih) {
		bcelMethod.getInstructionList().setPositions();
		return ih.getPosition();
	}
	
	/**
	 * Computes instructions pc numbers (for all instructions)
	 * and searches for instruction of given PC number.
	 * 
	 * @param pc - offset (program counter) of an instruction.
	 * @return instruction of given offset (from this method)
	 * 		or null if there is no such instruction.
	 */
	public InstructionHandle findAtPC(int pc) {
		InstructionList il = getInstructions();
		il.setPositions();
		Iterator iter = il.iterator();
		while (iter.hasNext()) {
			InstructionHandle ih = (InstructionHandle) (iter.next());
			if (ih.getPosition() == pc)
				return ih;
		}
		return null;
	}

	/**
	 * Seraches for local variable of given name.
	 * 
	 * @param name - name of local variable to look for.
	 * @return local variable of given name,
	 * 		or <code>null</code> if no variable could be found.
	 */
	public BCLocalVariable findLocalVariable(String name) {
		for (int i=0; i<lvars.length; i++)
			if (lvars[i].getName().equals(name))
				return lvars[i];
		return null;
	}
	
	/**
	 * @return attribute map.
	 */
	public BCAttributeMap getAmap() {
		return amap;
	}

	/**
	 * @return BCClass containing this method.
	 */
	public BCClass getBcc() {
		return bcc;
	}

	/**
	 * @return method specification
	 */
	public MethodSpecification getMspec() {
		return mspec;
	}

	/**
	 * Sets method specification attribute for this method.
	 * 
	 * @param mspec - new method specification.
	 */
	public void setMspec(MethodSpecification mspec) {
		this.mspec = mspec;
	}

	/**
	 * @return BCEL method generator. Use this instead of
	 * 		creating new on from BCEL Method.
	 */
	public MethodGen getBcelMethod() {
		return bcelMethod;
	}

	/**
	 * @return number of local variables.
	 */
	public int getLocalVariableCount() {
		return lvars.length;
	}
	
	/**
	 * Returns local variable of given index.
	 * 
	 * @param index - number of local variable
	 * 		(in this method),
	 * @return <code>index</code>-th local variable of this
	 * 		method.
	 */
	public BCLocalVariable getLocalVariable(boolean isOld, int index) {
		if (isOld)
			return oldvars[index];
		return lvars[index];
	}

}
