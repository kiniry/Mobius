package annot.attributes;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;

public class BCAttributeMap {

	private BCMethod method;
	private int length;
	private HashMap<InstructionHandle, SingleList> map;

	private AssertTable atab;

	public BCAttributeMap(BCMethod m) {
		this.method = m;
		this.atab = new AssertTable(m, this);
		this.length = 0;
		this.map = new HashMap<InstructionHandle, SingleList>();
	}

	public void addAttribute(InCodeAttribute ica) {
		addAttribute(ica, -1);
	}

	@Deprecated
	public InCodeAttribute addAttribute(int atype, int pc, int minor) {
		switch (atype) {
		case AType.C_ASSERT:
			SingleAssert sa = new SingleAssert(method, method.findAtPC(pc),
					minor);
			addAttribute(sa, minor);
			return sa;
		default:
			throw new RuntimeException("invalid attribute type");
		}
	}

	public void addAttribute(InCodeAttribute ica, int minor) {
		if (ica.getIh() == null)
			throw new RuntimeException("InstructionHandle not set");
		ica.setMinor(minor);
		if (map.containsKey(ica.getIh())) {
			map.get(ica.getIh()).addAttribute(ica);
		} else {
			SingleList sl = new SingleList();
			sl.addAttribute(ica);
			map.put(ica.getIh(), sl);
		}
		length++;
	}

	public void removeAttribute(InCodeAttribute ica) {
		if (!map.containsKey(ica.getIh()))
			throw new RuntimeException("attribute not found!");
		map.get(ica.getIh()).removeAttribute(ica);
		length--;
	}

	public void removeAll() {
		Iterator<SingleList> iter = map.values().iterator();
		while (iter.hasNext()) {
			SingleList sl = iter.next();
			sl.removeAll();
		}
		map.clear();
		length = 0;
	}

	public void replaceAttribute(InCodeAttribute olda, InCodeAttribute newa) {
		if (!map.containsKey(olda.getIh()))
			throw new RuntimeException("attribute not found!");
		newa.setIh(olda.getIh());
		newa.setMinor(olda.getMinor());
		SingleList sl = map.get(olda.getIh());
		sl.replace(olda, newa);
	}

	public SingleList getAllAt(InstructionHandle ih) {
		SingleList sl = map.get(ih);
		if (sl == null)
			return new SingleList();
		return sl;
	}

	public InCodeAttribute[] getAllAttributes(int types) {
		InCodeAttribute[] all = new InCodeAttribute[length];
		LinkedList<SingleList> ll = new LinkedList<SingleList>();
		Iterator<SingleList> iter1 = map.values().iterator();
		while (iter1.hasNext())
			ll.addLast(iter1.next());
		Collections.sort(ll);
		Iterator<SingleList> iter = ll.iterator();
		int i = 0;
		while (iter.hasNext()) {
			SingleList sl = iter.next();
			InCodeAttribute[] some = sl.getAll(types);
			for (int j = 0; j < some.length; j++)
				all[i++] = some[j];
		}
		return all;
	}

	public int getLength() {
		return length;
	}

	public AssertTable getAtab() {
		return atab;
	}

}
