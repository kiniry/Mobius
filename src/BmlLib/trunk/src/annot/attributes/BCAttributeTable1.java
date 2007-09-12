package annot.attributes;

import annot.bcclass.BCMethod;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;

public abstract class BCAttributeTable1 implements IBCAttribute {

	protected BCMethod method;
	protected BCAttributeMap parent;

	public BCAttributeTable1(BCMethod m, BCAttributeMap parent) {
		this.method = m;
		this.parent = parent;
	}

	public int getIndex() {
		return method.bcc.cp.findConstant(getName()).getIndex();
	}

	public abstract String getName();

	public abstract int singleType();

	public abstract InCodeAttribute loadSingle(BCMethod m, AttributeReader ar)
			throws ReadAttributeException;

	public void load(AttributeReader ar) throws ReadAttributeException {
		parent.removeAll();
		int n = ar.readAttributesCount();
		for (int i = 0; i < n; i++) {
			int pc = ar.readShort();
			InCodeAttribute ica = loadSingle(method, ar);
			ica.ih = method.findAtPC(pc);
			if (ica.ih == null)
				throw new ReadAttributeException("Attribute unplaceble: pc="
						+ pc);
			parent.addAttribute(ica);
		}
	}

	public void save(AttributeWriter aw) {
		aw.writeAttributeCount(parent.getLength());
		InCodeAttribute[] all = parent.getAllAttributes(singleType());
		for (int i = 0; i < all.length; i++) {
			aw.writeShort(all[i].getPC());
			all[i].saveSingle(aw);
		}
	}

}
