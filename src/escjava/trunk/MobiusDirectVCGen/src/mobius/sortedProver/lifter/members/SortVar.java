/**
 * 
 */
package mobius.sortedProver.lifter.members;

import javafe.util.Assert;
import javafe.util.ErrorSet;
import mobius.sortedProver.EscNodeBuilder;
import mobius.sortedProver.Lifter;
import mobius.sortedProver.nodebuilder.members.Sort;

public class SortVar extends Sort
	{
		private /*@ nullable @*/Sort ref;
		
		public SortVar()
		{
			super("sortVar", null, null, null);
		}
		
		void refSet()
		{
			if (ref == null) {
				//if (dumpBuilder != null)
					ref = Lifter.sortRef;
//				else
//					Assert.fail("ref == null");
			}
		}
		
		public /*@ nullable @*/Sort getSuperSort()
		{
			refSet();
			return ref.getSuperSort();
		}

		public /*@ nullable @*/Sort getMapFrom()
		{
			refSet();			
			return ref.getMapFrom();
		}

		public /*@ nullable @*/Sort getMapTo()
		{
			refSet();			
			return ref.getMapTo();
		}
		
		public boolean isFinalized()
		{
			if (ref == null) return false;
			if (ref instanceof SortVar)
				return ((SortVar)ref).isFinalized();
			return true;
		}
		
		boolean occurCheck(Sort s)
		{
			if (s == this)
				return true;
				
			if (s instanceof SortVar && !((SortVar)s).isFinalized())
			{
				return false;
			}
			else if (s.getMapFrom() != null) {
				return occurCheck(s.getMapFrom()) || occurCheck(s.getMapTo());
			} else return false;
		}
		
		public void assign(Sort s)
		{
			Assert.notFalse(ref == null);
			if (Lifter.doTrace)
				Lifter.trace("assign: ?" + id + " <- " + s);
			if (occurCheck(s))
				ErrorSet.error("cyclic sort found");
			else
				ref = s;
		}
		
		public Sort theRealThing(EscNodeBuilder builder)
		{
			if (builder != null)
				refSet();
			
			if (ref != null && ref instanceof SortVar)
				return ref.theRealThing();
			return ref == null ? this : ref;
		}
		
		public String toString()
		{
			if (ref == null) return "?" + id;
			else return ref.toString();
		}
	}