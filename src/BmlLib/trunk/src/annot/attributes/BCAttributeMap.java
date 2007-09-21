package annot.attributes;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;

/**
 * This class represents collection of all annotations inside
 * <code>method</code>'s body.
 * (one BCAttributeMap for each method)
 * 
 * @author tomekb
 */
public class BCAttributeMap {

	/**
	 * The method mentioned in headers comment.
	 */
	private BCMethod method;

	/**
	 * Single annotations count.
	 */
	private int length;

	/**
	 * Hash map containing lists of annotations for each
	 * instruction in the method.
	 */
	private HashMap<InstructionHandle, SingleList> map;

	/**
	 * Method's attribute used for loading attributes from
	 * and saving them to .class file (to BCEL method).
	 */
	private AssertTable atab;

	/**
	 * Constructor from a method that creates
	 * an empty collection.
	 * 
	 * @param m - the method.
	 */
	public BCAttributeMap(BCMethod m) {
		this.method = m;
		this.atab = new AssertTable(m, this);
		this.length = 0;
		this.map = new HashMap<InstructionHandle, SingleList>();
	}

	/**
	 * Adds an annotation to the collection (as an last 
	 * annotation for it's instruction).
	 * 
	 * @param ica - an attribute to be added.
	 */
	public void addAttribute(InCodeAttribute ica) {
		addAttribute(ica, -1);
	}

	/**
	 * Adds an empty annotation of given type, pc and minor.
	 * 
	 * @param atype - type of annotation
	 * 		(from AType interface),
	 * @param pc - current pc number of instruction to add
	 * 		new annotation before,
	 * @param minor - minor number of inserted annotation
	 * 		(for annotation ordering for single instruction).
	 * @return inserted annotation.
	 */
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

	/**
	 * Adds an annotation with given minor number to the
	 * collection.
	 * 
	 * @param ica - annotation to be added. Must have set
	 * 		ih (instructionHandle) attribute,
	 * @param minor - position of annotation within
	 * 		its instruction. Annotation will be inserted
	 * 		after last annotation for its instruction
	 * 		with less or equal minor number than this
	 * 		parameter. 
	 */
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

	/**
	 * Removes given annotation from the collection.
	 * 
	 * @param ica - annotation to be removed.
	 */
	public void removeAttribute(InCodeAttribute ica) {
		if (!map.containsKey(ica.getIh()))
			throw new RuntimeException("attribute not found!");
		map.get(ica.getIh()).removeAttribute(ica);
		length--;
	}

	/**
	 * Clears the collection (removes all annotations).
	 */
	public void removeAll() {
		Iterator<SingleList> iter = map.values().iterator();
		while (iter.hasNext()) {
			SingleList sl = iter.next();
			sl.removeAll();
		}
		map.clear();
		length = 0;
	}

	/**
	 * Replaces given annotations from this collection
	 * with another one. New annotation will be placed
	 * in the same place as the old one, regardless of
	 * its ih and minor attributes.
	 * 
	 * @param olda - annotation to be removed,
	 * @param newa - annotation to be inserted
	 * 		in <code>olda</code>'s place.
	 */
	public void replaceAttribute(InCodeAttribute olda, InCodeAttribute newa) {
		if (!map.containsKey(olda.getIh()))
			throw new RuntimeException("attribute not found!");
		newa.setIh(olda.getIh());
		newa.setMinor(olda.getMinor());
		SingleList sl = map.get(olda.getIh());
		sl.replace(olda, newa);
	}

	/**
	 * Returns lists of all annotations for given instruction.
	 * 
	 * @param ih - given instruction handle.
	 * @return SingleList of annotation for given instruction
	 * 		(or an new empty list if there are no annotations
	 * 		for given instruction).
	 */
	public SingleList getAllAt(InstructionHandle ih) {
		SingleList sl = map.get(ih);
		if (sl == null)
			return new SingleList(); //XXX new?
		return sl;
	}

	/**
	 * Gives all annotations of given type from the collection.
	 * 
	 * @param types - attribute types mask (from ATypes).
	 * @return array of annotations matching given type mask.
	 */
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

	/**
	 * @return total annotation count.
	 */
	public int getLength() {
		return length;
	}

	/**
	 * @return assert table for file I/O.
	 */
	public AssertTable getAtab() {
		return atab;
	}

}
