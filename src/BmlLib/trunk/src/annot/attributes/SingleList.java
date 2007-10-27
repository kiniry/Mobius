package annot.attributes;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.textio.BMLConfig;
import annot.textio.Parsing;

/**
 * This class represents list of annotations attached
 * to single bytecode instruction handle.
 * 
 * @author tomekb
 */
public class SingleList implements Comparable<SingleList> {

	/**
	 * Collection containing the annotations.
	 */
	private LinkedList<InCodeAttribute> attributes;

	/**
	 * Bytecode instruction that all annotations from this
	 * list are attached to.
	 */
	private InstructionHandle ih;
	
	/**
	 * Method containing instruction whose comment this
	 * list represents.
	 */
	private BCMethod method;
	
	/**
	 * A standard constructor. Creates an empty list.
	 * This list will contain all annotations attached
	 * to given <code>instruction</code>.
	 * 
	 * @param method - method of an bytecode instruction
	 * 		for this list.
	 * @param ih - bytecode instruction for this list.
	 */
	public SingleList(BCMethod method, InstructionHandle ih) {
		this.method = method;
		this.ih = ih;
		attributes = new LinkedList<InCodeAttribute>();
	}

	/**
	 * Sorts and returns all annotations from this list
	 * of given types.
	 * 
	 * @param types - bitmask representing a set of annotation
	 * 		types from AType interface;
	 * @return Array of all annotations from this list matching
	 * 		given type (it's type & types > 0), sorted by
	 * 		their's minor numbers.
	 */
	public InCodeAttribute[] getAll(int types) {
		Collections.sort(attributes);
		InCodeAttribute[] all = attributes
				.toArray(new InCodeAttribute[attributes.size()]);
		int n = 0;
		for (int i = 0; i < all.length; i++)
			if ((all[i].aType() & types) > 0)
				n++;
		InCodeAttribute[] filtered = new InCodeAttribute[n];
		int pos = 0;
		for (int i = 0; i < all.length; i++)
			if ((all[i].aType() & types) > 0) {
				MLog.putMsg(MLog.PDebug, all[i].getPC() + "; "
						+ all[i].getMinor());
				filtered[pos++] = all[i];
			}
		return filtered;
	}

	public int getAttributeCount(int types) {
		int cnt = 0;
		Iterator<InCodeAttribute> i = attributes.iterator();
		while (i.hasNext()) {
			if ((i.next().aType() & types) > 0)
				cnt++;
		}
		return cnt;
	}

	/**
	 * Prints all its annotations to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of all annotations
	 * 		in one comment.
	 */
	public String printCode(BMLConfig conf) {
		String code = "";
		Iterator<InCodeAttribute> iter = attributes.iterator();
		while (iter.hasNext())
			code += iter.next().printCode(conf);
		return Parsing.addComment(code);
	}

	/**
	 * Adds an annotaton to the list, updating minor numbers
	 * to ensure no two annotations from it has the same minor
	 * number and saving list's ordering (no annotations are
	 * swapped on the list and list is still sorted).
	 * 
	 * @param ica - annotation to be added.
	 */
	public void addAttribute(InCodeAttribute ica) {
		if (ica.getMinor() == -1) {
			if (attributes.size() == 0) {
				ica.setMinor(0);
			} else {
				ica.setMinor(attributes.getLast().getMinor() + 1);
			}
		}
		if (attributes.size() > 0)
			if (attributes.getFirst().getIh() != ica.getIh())
				throw new RuntimeException(
						"difrent instruction's annotations in one SingleList");
		int m = ica.getMinor();
		Iterator<InCodeAttribute> iter = attributes.iterator();
		InCodeAttribute prev = null;
		while (iter.hasNext()) {
			InCodeAttribute a = iter.next();
			if (a.getMinor() >= m)
				prev = a;
		}
		if (prev == null) {
			attributes.addLast(ica);
		} else {
			attributes.add(attributes.indexOf(prev), ica); // ?
		}
		iter = attributes.iterator();
		int minor = -1;
		int inc = 0;
		while (iter.hasNext()) {
			InCodeAttribute a = iter.next();
			if (a.getMinor() + inc == minor)
				inc++;
			minor = a.getMinor();
			a.setMinor(a.getMinor() + inc);
		}
	}

	/**
	 * Removes annotation from the list.
	 * 
	 * @param ica - annotation to be removed.
	 */
	public void removeAttribute(InCodeAttribute ica) {
		attributes.remove(ica);
	}

	/**
	 * Clears the list, removing all annotations from it.
	 */
	public void removeAll() {
		attributes.clear();
	}

	/**
	 * Replaces an annotation from the list with another one.
	 * They should have both the same minor numbers.
	 * 
	 * @param olda - annotation to be removed,
	 * @param newa - annotation to be added
	 * 		at <code>olda</code>'s place.
	 */
	public void replace(InCodeAttribute olda, InCodeAttribute newa) {
		if (!attributes.contains(olda))
			throw new RuntimeException(
					"(SingleList.replace): attribute not found!");
		attributes.set(attributes.indexOf(olda), newa);
	}

	/**
	 * Returns an annotation from the list with given
	 * minor number.
	 * 
	 * @param minor - minor number of returned annotation.
	 * @return An annotation with minor number equal to the
	 * 		given one, or null if no annotations with such
	 * 		minor number could be found.
	 */
	public InCodeAttribute get(int minor) {
		Iterator<InCodeAttribute> iter = attributes.iterator();
		while (iter.hasNext()) {
			InCodeAttribute ica = iter.next();
			if (ica.getMinor() == minor)
				return ica;
		}
		return null;
	}

	/**
	 * Returns <code>n</code>-th annotation from the list.
	 * 
	 * @param n - position of annotation (number of annotations
	 * 		displayed before it for the same instruction).
	 * @return <code>n</code>-th annotation from this list.
	 */
	public InCodeAttribute nth(int n) {
		return attributes.get(n);
	}

	/**
	 * Replaces n-th annotation from this list with given one
	 * (or appends it to the list, if <code>n > size</code>).
	 * 
	 * @param n - position of annotation to be replaced
	 * @param ica - annotation to replace <code>n</code>-th
	 * 		annotation from list.
	 */
	public void setNth(int n, InCodeAttribute ica) {
		if (n < attributes.size()) {
			nth(n).replaceWith(ica);
		} else {
			ica.setMinor(-1);
			addAttribute(ica);
		}
	}
	
	/**
	 * Removes all except first <code>n</code> annotations
	 * from list.
	 * 
	 * @param n - number of annotations that should left
	 * 		on the list.
	 */
	public void trunce(int n) {
		if (n < 0)
			throw new RuntimeException("invalid argument value: " + n);
		while (attributes.size() > n)
			attributes.removeLast();
	}
	
	/**
	 * @return pc numner of annotation's bytecode instruction,
	 * 		or -1 if list is empty.
	 */
	@Deprecated
	public int getPC() {
		return method.getPC(ih);
	}

	/**
	 * @return position in method's instruction list. This
	 * 		should be more reliable than {@link #getPC()}.
	 */
	public int getPosition() {
		InstructionHandle[] handles = method.getInstructions().getInstructionHandles();
		for (int i=0; i<handles.length; i++)
			if (ih == handles[i])
				return i;
		return -1;
	}
	
	/**
	 * @return bytecode instruction that all annotations from this
	 * list are attached to.
	 */
	public InstructionHandle getIh() {
		return ih;
	}

	/**
	 * @return length of this list.
	 */
	public int size() {
		return attributes.size();
	}
	
	/**
	 * compares this annotation list to given one in order they
	 * should appead in String representation of a method.
	 * Both annotation lists should be from the same method.
	 * @param o - annotation list to compare to.
	 * @return a positive integer if <code>o</code> is above
	 * 		this annotation list in String representation
	 * 		of method, a negative integer if <code>o</code>
	 * 		is below, and zero if <code>o</code> is the same
	 * 		annotation list.
	 */
	public int compareTo(SingleList o) {
		return getPosition() - o.getPosition();
	}

}
