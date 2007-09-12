package annot.attributes;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;

import annot.bcclass.MLog;
import annot.textio.BMLConfig;

public class SingleList implements Comparable<SingleList> {

	private LinkedList<InCodeAttribute> attributes;

	public SingleList() {
		attributes = new LinkedList<InCodeAttribute>();
	}

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
				MLog.putMsg(MLog.PDebug, all[i].getPC() + "; " + all[i].minor);
				filtered[pos++] = all[i];
			}
		return filtered;
	}

	public String printCode(BMLConfig conf) {
		String code = "";
		Iterator<InCodeAttribute> iter = attributes.iterator();
		while (iter.hasNext())
			code += iter.next().printCode(conf);
		return conf.addComment(code);
	}

	public void addAttribute(InCodeAttribute ica) {
		if (ica.minor == -1) {
			if (attributes.size() == 0) {
				ica.minor = 0;
			} else {
				ica.minor = attributes.getLast().minor + 1;
			}
		}
		if (attributes.size() > 0)
			if (attributes.getFirst().ih != ica.ih)
				throw new RuntimeException(
						"difrent instruction's annotations in one SingleList");
		int m = ica.minor;
		Iterator<InCodeAttribute> iter = attributes.iterator();
		InCodeAttribute prev = null;
		while (iter.hasNext()) {
			InCodeAttribute a = iter.next();
			if (a.minor >= m)
				prev = a;
		}
		if (prev == null) {
			attributes.addLast(ica);
		} else {
			attributes.add(attributes.indexOf(prev), ica); // XXX ??
		}
		iter = attributes.iterator();
		int minor = -1;
		int inc = 0;
		while (iter.hasNext()) {
			InCodeAttribute a = iter.next();
			if (a.minor + inc == minor)
				inc++;
			minor = a.minor;
			a.minor += inc;
		}
	}

	public void removeAttribute(InCodeAttribute ica) {
		attributes.remove(ica);
	}

	public void removeAll() {
		attributes.clear();
	}

	public void replace(InCodeAttribute olda, InCodeAttribute newa) {
		if (!attributes.contains(olda))
			throw new RuntimeException(
					"(SingleList.replace): attribute not found!");
		attributes.set(attributes.indexOf(olda), newa);
	}

	public InCodeAttribute get(int minor) {
		Iterator<InCodeAttribute> iter = attributes.iterator();
		while (iter.hasNext()) {
			InCodeAttribute ica = iter.next();
			if (ica.minor == minor)
				return ica;
		}
		return null;
	}

	public int getPC() {
		if (attributes.size() == 0)
			return -1;
		return attributes.getFirst().getPC();
	}

	public int compareTo(SingleList o) {
		return getPC() - o.getPC();
	}

}
