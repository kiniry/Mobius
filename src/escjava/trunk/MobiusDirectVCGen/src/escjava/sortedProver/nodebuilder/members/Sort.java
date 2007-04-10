/**
 * 
 */
package escjava.sortedProver.nodebuilder.members;

import java.util.Hashtable;


public class Sort extends Symbol
{
	private final /*@ nullable @*/Sort superSort;
	private final /*@ nullable @*/Sort mapFrom;
	private final /*@ nullable @*/Sort mapTo;
	
	public Sort(String name, Sort superSort, /*@ nullable @*/Sort mapFrom, /*@ nullable @*/Sort mapTo)
	{
		super(name);
		this.superSort = superSort;
		this.mapFrom = mapFrom;
		this.mapTo = mapTo;
	}
	
	public boolean isSubSortOf(Sort other)
	{
		other = other.theRealThing();
		Sort th = theRealThing();
		if (th == other)
			return true;
		if (th.getSuperSort() == null)
			return false;
		return th.getSuperSort().isSubSortOf(other);
	}
	
	// TODO use HashSet
	public /*@ nullable @*/Sort commonSuperSort(Sort other)
	{
		Hashtable h = new Hashtable();
		for (Sort s = this; s != null; s = s.getSuperSort())
			h.put(s, s);
		for (Sort s = other; s != null; s = s.getSuperSort())
			if (h.containsKey(s))
				return s;
		return null;
	}

	public /*@ nullable @*/Sort getSuperSort()
	{
		return theRealThing().superSort;
	}

	public /*@ nullable @*/Sort getMapFrom()
	{
		return theRealThing().mapFrom;
	}

	public /*@ nullable @*/Sort getMapTo()
	{
		return theRealThing().mapTo;
	}
	
	public String toString()
	{
		if (getMapFrom() != null)
			return getSuperSort().name + "[" + getMapFrom() + "," + getMapTo() + "]";
		else
			return theRealThing().name;
	}
	
	public Sort theRealThing()
	{
		return this;
	}
}