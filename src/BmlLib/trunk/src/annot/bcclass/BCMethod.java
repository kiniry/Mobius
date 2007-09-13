package annot.bcclass;

import java.util.Iterator;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.MethodGen;

import annot.attributes.AType;
import annot.attributes.BCAttributeMap;
import annot.attributes.InCodeAttribute;
import annot.attributes.MethodSpecification;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public class BCMethod {

	private final static boolean displayStyle = false;

	public BCClass bcc;
	private MethodGen bcelMethod;
	public MethodSpecification mspec;
	public BCAttributeMap amap;

	public BCMethod(BCClass bcc, MethodGen m) throws ReadAttributeException {
		MLog.putMsg(MLog.PInfo, "  initializing method: " + m.getName());
		this.bcc = bcc;
		this.bcelMethod = m;
		this.amap = new BCAttributeMap(this);
		Attribute[] attrs = m.getAttributes();
		AttributeReader ar = new AttributeReader(this);
		for (int i = 0; i < attrs.length; i++) {
			if (attrs[i] instanceof Unknown)
				ar.readAttribute((Unknown) attrs[i]);
		}
	}

	@Override
	public String toString() {
		return bcelMethod.toString() + "\n";
	}

	public String printCode(BMLConfig conf) {
		String code = "";
		if (mspec != null)
			code += mspec.printCode(conf);
		code += toString();
		String bcode = "";
		if (displayStyle) {
			InstructionList il = bcelMethod.getInstructionList();
			il.setPositions();
			Iterator<InstructionHandle> iter = bcelMethod.getInstructionList()
					.iterator();
			while (iter.hasNext()) {
				InstructionHandle ih = iter.next();
				bcode += amap.getAllAt(ih).printCode(conf);
				bcode += ih.getPosition()
						+ ": "
						+ ih.getInstruction()
								.toString(bcc.jc.getConstantPool()) + "\n";
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
				bcode += conf.addComment(annotLines) + line + "\n";
			}
		}
		return code + bcode;
	}

	public void addAttribute(InCodeAttribute ica) {
		MLog.putMsg(MLog.PProgress, "adding attribute: " + ica.toString());
		amap.addAttribute(ica, ica.minor);
	}

	public Method save() {
		MLog.putMsg(MLog.PInfo, "  saving method: " + bcelMethod.getName());
		AttributeWriter aw = new AttributeWriter(this);
		Attribute[] attrs = BCClass.removeBMLAttributes(bcelMethod
				.getAttributes());
		if (mspec != null)
			attrs = BCClass.addAttribute(attrs, aw.writeAttribute(mspec));
		if (amap.getLength() > 0)
			attrs = BCClass.addAttribute(attrs, aw.writeAttribute(amap.atab));
		bcelMethod.removeAttributes();
		for (int i = 0; i < attrs.length; i++)
			bcelMethod.addAttribute(attrs[i]);
		bcelMethod.update();
		bcelMethod.setMaxStack();
		bcelMethod.setMaxLocals();
		return bcelMethod.getMethod();
	}

	public InstructionList getInstructions() {
		return bcelMethod.getInstructionList();
	}

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

}
