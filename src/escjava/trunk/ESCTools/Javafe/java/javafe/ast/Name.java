/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/* ---------------------------------------------------------------------- */

/**
 ** Treated as an immutable type. <p>
 **
 ** Invariant: There is always at least one element in a Name.<p>
 **/

public abstract class Name extends ASTNode {

    /**
     ** Return our printname, which will be of one of the forms X, X.Y,
     ** X.Y.Z, ...
     **/
    //@ ensures \result!=null
    public abstract String printName();

    /**
     ** Return a hash code for <code>this</code> such that two
     ** <code>Name</code>s that are <code>equals</code> have the same
     ** hash code.
     **/
    public abstract int hashCode();

    /**
     ** Return true if <code>other</code> is a <code>Name</code> that
     ** is component-wise equal to <code>this</code>.
     **/
    public abstract boolean equals(Object other);



    /**
     ** The number of identifiers we contain
     **/
    //@ invariant length>=1
    /*@ ghost public int length; */

    /** Return the number of identifiers in <code>this</code>. */
    //@ ensures \result==length
    public abstract int size();


    /**
     ** Return the ith identifier of <code>this</code>.
     **/
    //@ requires 0<=i && i<length
    //@ ensures \result!=null
    public abstract Identifier identifierAt(int i);

    /**
     ** Return the location of the ith identifier of <code>this</code>.
     **/
    //@ requires 0<=i && i<length
    //@ ensures \result!=Location.NULL
    public abstract int locIdAt(int i);

    /**
     ** Return the location of the dot after the ith identifier of
     ** <code>this</code>.
     **/
    //@ requires 0<=i && i<length-1
    //@ ensures \result!=Location.NULL
    public abstract int locDotAfter(int i);


    /**
     ** Return the first <code>len</code> identifiers in
     ** <code>this</code> in an array.  Requires that <code>len</code>
     ** be between 0 and length of <code>this</code> inclusive.
     **/
    //@ requires 0<=len && len<=length
    //@ ensures \nonnullelements(\result)
    //@ ensures \result.length == len
    public abstract String[] toStrings(int len);

    /**
     ** Return all identifiers in <code>this</code> in an array.
     **/
    //@ ensures \nonnullelements(\result)
    //@ ensures \result.length == length
    public String[] toStrings() {
	return toStrings(size());
    }



    /**
     ** Make a <code>Name</code> with the given identifiers and
     ** locations.  Caller must forget about the Vecs/arrays passed
     ** here.
     **/
    //@ requires ids!=null && locIds!=null && locDots!=null
    //@ requires ids.count>0
    //@ requires ids.count==locIds.length && ids.count==locDots.length+1
    /*@ requires (\forall int i; (0<=i && i<locIds.length)
			==> locIds[i]!=Location.NULL) */
    /*@ requires (\forall int i; (0<=i && i<locDots.length)
			==> locDots[i]!=Location.NULL) */
    //@ ensures \result!=null
    public static Name make(int[] locIds, int[] locDots, IdentifierVec ids) {
	int sz = ids.size();
	Assert.precondition(sz > 0 && locIds.length == sz
			&& locDots.length + 1 == sz);
	if (sz == 1)
	    return SimpleName.make(ids.elementAt(0), locIds[0]);
	else
	    return CompoundName.make(ids, locIds, locDots);
    }

    /**
     ** Make a <code>Name</code> whose locations are all
     ** <code>loc</code> from a <code>String</code>. <p>
     **
     ** Precondition: <code>N.length()>0</code><p>
     ** 
     ** This routine parses a non-empty <code>String</code> consisting
     ** of a series of dot-separated components into a <code>Name</code>.<p>
     **/
    //@ requires N!=null
    //@ requires N.count>0
    //@ requires loc!=Location.NULL
    //@ ensures \result!=null
    public static Name make(String N, int loc) {
	// Convert N to a list of its components:
	String[] components = javafe.filespace.StringUtil.parseList(N, '.');
	int sz = components.length;
	Assert.notFalse(sz>0);		//@ nowarn Pre

	// Convert the components to Identifiers:
	IdentifierVec ids = IdentifierVec.make();
	for(int i = 0; i < sz; i++)
	    ids.addElement(Identifier.intern(components[i]));


	if (sz == 1)
	    return SimpleName.make(ids.elementAt(0), loc);

	int[] newLocIds = new int[sz];
	int[] newLocDots = new int[sz-1];
	for(int i = 0; i < sz; i++)
	    newLocIds[i] = loc;
	for(int i = 0; i < sz-1; i++)
	    newLocDots[i] = loc;

	return make(newLocIds, newLocDots, ids);
    }



    /** Return a <code>Name</code> consisting of the first
     ** <code>len</code> identifiers of <code>this</code>.  Requires
     ** that <code>len</code> is greater than zero and less than or
     ** equal to the length of <code>this</code>.
     **/
    //@ requires 0<len && len<=length
    //@ ensures \result!=null
    public abstract Name prefix(int len);



    /**
     ** Override getEndLoc so it refers to the actual end of us.
     **/
    public int getEndLoc() {
	return Location.inc(getStartLoc(),
			    Math.max(0, printName().length()-1));
    }


    /**
     ** Avoid allocating more than one of these.
     **/
    //@ invariant \nonnullelements(emptyStringArray)
    //@ invariant emptyStringArray.length == 0
    protected static String[] emptyStringArray = new String[0];



// Generated boilerplate constructors:

   /**
    ** Construct a raw Name whose class invariant(s) have not
    ** yet been established.  It is the caller's job to
    ** initialize the returned node's fields so that any
    ** class invariants hold.
    **/
   //@ requires I_will_establish_invariants_afterwards
   protected Name() {}    //@ nowarn Invariant,NonNullInit

   public void check() {
      super.check();
   }

}
