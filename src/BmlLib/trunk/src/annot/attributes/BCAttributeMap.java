package annot.attributes;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.bcclass.MLog;

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
	 * May be out of date, use getLength() instead!
	 */
	@Deprecated
	private int length;

	/**
	 * Hash map containing lists of annotations for each
	 * instruction in the method.
	 */
	private HashMap<InstructionHandle, SingleList> map;

	/**
	 * Method's attribute used for loading asserts from
	 * and saving them to .class file (to BCEL method).
	 */
	private AssertTable atab;

	/**
	 * Method's attribute used for loading loop specifications
	 * from and saving them to .class file (to BCEL method).
	 */
	private LoopSpecificationTable lstab;

	/**
	 * Constructor from a method that creates
	 * an empty collection.
	 * 
	 * @param m - the method.
	 */
	public BCAttributeMap(BCMethod m) {
		this.method = m;
		this.atab = new AssertTable(m, this);
		this.lstab = new LoopSpecificationTable(m, this);
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
		case AType.C_LOOPSPEC:
			SingleLoopSpecification sls = new SingleLoopSpecification(
					method, method.findAtPC(pc), minor, null, null, null);
			addAttribute(sls, minor);
			return sls;
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
			SingleList sl = new SingleList(method, ica.getIh());
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
			return new SingleList(method, ih); //XXX new?
		return sl;
	}

	/**
	 * Gives all annotations of given type from the collection.
	 * 
	 * @param types - attribute types mask (from ATypes).
	 * @return array of annotations matching given type mask.
	 */
	public InCodeAttribute[] getAllAttributes(int types) {
		InCodeAttribute[] all = new InCodeAttribute[getAttributeCount(types)];
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
	 * Replaces current annotation list for given instruction
	 * handle with given one.
	 * 
	 * @param ih - instruction whose annotation list should
	 * 		be replaced,
	 * @param sl - new annotations list.
	 */
	public void setAtributesForInstruction(InstructionHandle ih, SingleList sl) {
		MLog.putMsg(MLog.PInfo, "singleList replaced");
		map.put(ih, sl);
	}
	
	/**
	 * Computes total count of annotations in this map.
	 * 
	 * @return total annotation count.
	 */
	public int getLength() {
		int l = 0;
		Iterator<SingleList> iter1 = map.values().iterator();
		while (iter1.hasNext())
			l += iter1.next().size();
		return l;
	}

	public int getAttributeCount(int types) {
		int cnt = 0;
		Iterator<SingleList> iter1 = map.values().iterator();
		while (iter1.hasNext())
			cnt += iter1.next().getAttributeCount(types);
		return cnt;
	}

	/**
	 * @return assert table for file I/O.
	 */
	public AssertTable getAtab() {
		return atab;
	}

	public LoopSpecificationTable getLstab() {
		return lstab;
	}

}
