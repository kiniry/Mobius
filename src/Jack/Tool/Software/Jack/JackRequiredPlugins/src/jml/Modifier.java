// @(#)$Id: Modifier.java,v 1.19 2001/08/03 00:58:21 leavens Exp $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


package jml;

//import edu.iastate.cs.jml.models.JMLType;

/** a Java or JML modifier
 *  @author Clyde Ruby, Yogy Namara, and Gary T. Leavens
 **/
public /*@ pure @*/ class Modifier implements JMLType
{

    // Each modifier is denoted by a single bit based on the 
    // following 'meaning' table.  This is used in ModifierSet (q.v.).
    // So it's important to add new modifiers are added in two places below!

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	public static final String meaning[] = new String[]
    { "", "(default privacy)",
      "public", "protected", "private", "static", "final", 
      "abstract", "transient", "native",
      "synchronized", "volatile", "strictfp", "const", 
      // for the is_JML_Modifier method, all the JML modifiers have to go below
      "model", "pure", "instance",
      "spec_protected", "spec_public", "monitored",
      "uninitialized", "ghost", "non_null" };

    // Add new modifiers above as an element of 'meaning'; and below !!!

    public static final Modifier NONE = new Modifier("");
    public static final Modifier DEFAULT = new Modifier("(default privacy)");
    public static final Modifier PUBLIC = new Modifier("public");
    public static final Modifier PROTECTED = new Modifier("protected");
    public static final Modifier PRIVATE = new Modifier("private");
    public static final Modifier STATIC = new Modifier("static");
    public static final Modifier FINAL = new Modifier("final");
    public static final Modifier ABSTRACT = new Modifier("abstract");
    public static final Modifier TRANSIENT = new Modifier("transient");
    public static final Modifier NATIVE = new Modifier("native");
    public static final Modifier SYNCHRONIZED = new Modifier("synchronized");
    public static final Modifier VOLATILE = new Modifier("volatile");
    public static final Modifier STRICTFP = new Modifier("strictfp");
    public static final Modifier CONST = new Modifier("const");
    // JML modifiers below here
    public static final Modifier MODEL = new Modifier("model");
    public static final Modifier PURE = new Modifier("pure");
    public static final Modifier INSTANCE = new Modifier("instance");
    public static final Modifier SPEC_PROTECTED = new Modifier("spec_protected");
    public static final Modifier SPEC_PUBLIC = new Modifier("spec_public");
    public static final Modifier MONITORED = new Modifier("monitored");
    public static final Modifier UNINITIALIZED = new Modifier("uninitialized");
    public static final Modifier GHOST = new Modifier("ghost");
    public static final Modifier NON_NULL = new Modifier("non_null");


    //@ public model final int meaning_index;
    //@ public invariant 0 <= meaning_index && meaning_index < meaning.length;

    protected final long modifier;
    protected final String strMod;

    //@ protected depends meaning_index <- modifier, strMod;

    /*@ protected invariant modifier >= 0;
      @ protected represents meaning_index \such_that
      @      (meaning_index == 0 ==> modifier == 0)
      @   && (meaning_index > 0
      @        ==> (Math.round(Math.pow(2, meaning_index-1)) == modifier));
      @ protected invariant_redundantly (* modifier is 0 or a power of 2 *);
      @*/

    /*@ protected invariant strMod != null;
      @ protected represents meaning_index \such_that
      @        meaning[meaning_index].equals(strMod);
      @*/

    /*@  public normal_behavior
      @    assignable meaning_index;
      @    ensures meaning_index == 0;
      @ implies_that
      @    ensures this.equals(Modifier.NONE);
      @*/
    public Modifier()
    {
        modifier = 0;
        strMod = "";
    }

    /*@  public normal_behavior
      @    requires mod != null && (* mod is a member of meaning *);
      @    assignable meaning_index;
      @    ensures meaning[meaning_index].equals(mod);
      @ implies_that
      @   protected normal_behavior
      @     requires mod != null && (* mod is a member of meaning *);
      @     assignable meaning_index, modifier, strMod;
      @     ensures strMod.equals(mod);
      @*/
    public Modifier(String mod)
    {
        strMod = mod;
        modifier = modifier_from_string(mod);
    }

    //@ requires mod != null && (* mod is a member of meaning *);
    private static long modifier_from_string(String mod)
    {
        long temp_modifier = 0;
        if (!mod.equals("")) {
            temp_modifier = 0x0001;
            int mi=1; 
            while (mi<meaning.length && !mod.equals(meaning[mi])) {
                temp_modifier = temp_modifier << 1;
                mi++;
            }
        }
        return temp_modifier;
    }

    /*@  public normal_behavior
      @    requires mod == 0
      @      || (\exists int mi; 0 <= mi && mi < meaning.length;
      @                          Math.round(Math.pow(2, mi-1)) == mod);
      @    assignable meaning_index;
      @    ensures Math.round(Math.pow(2, meaning_index-1)) == mod;
      @ implies_that
      @   protected normal_behavior
      @     requires mod == 0
      @      || (\exists int mi; 0 <= mi && mi < meaning.length;
      @                          Math.round(Math.pow(2, mi-1)) == mod);
      @     assignable meaning_index, modifier, strMod;
      @     ensures modifier == mod;
      @*/
    public Modifier(long mod)
    {
        modifier = mod;
        strMod = strMod_from_long(mod);
    }

    /*@ requires mod == 0
      @       || (\exists int mi; 0 <= mi && mi < meaning.length;
      @                           Math.round(Math.pow(2, mi-1)) == mod);
      @*/
    private static String strMod_from_long(long mod)
    {

        long temp_modifier = 0x0001;
        String err_string = "(error)";
        String temp_strMod = err_string;
        for (int mi=1; mi<meaning.length; mi++) {
            if (temp_modifier == mod) {
                temp_strMod = meaning[mi];
                break;
            }
            temp_modifier = temp_modifier << 1;
        }
        return temp_strMod;
    }

    //@ ensures \result == Math.round(Math.pow(2, meaning_index-1));
    public long getModifier()
    {
        return modifier;
    }

    public boolean equals (Object o)
    {
        if (o instanceof Modifier) {
            return (modifier == ((Modifier)o).modifier);
        } else {
            return false;
        }
    }

    public Object clone ()
    {
        return this;
    }

    /*@  public normal_behavior
      @    requires meaning_index <= 1;
      @    ensures "".equals(\result);
      @   also
      @    requires meaning_index > 1;
      @    ensures meaning[meaning_index].equals(\result);
      @*/
    public String toString()
    {
        if (modifier == Modifier.DEFAULT.modifier) {
            return "";
        } else {
            return strMod;
        }
    }

    /*@  public normal_behavior
      @    requires mod == 0
      @      || (\exists int mi; 0 <= mi && mi < meaning.length;
      @                          Math.round(Math.pow(2, mi-1)) == mod);
      @    {|
      @      old model Modifier m = new Modifier(mod);
      @      ensures \result <==>
      @           m.equals(MODEL) || m.equals(PURE)
      @           || m.equals(INSTANCE) || m.equals(SPEC_PROTECTED)
      @           || m.equals(SPEC_PUBLIC) || m.equals(MONITORED)
      @           || m.equals(UNINITIALIZED) || m.equals(GHOST);
      @    |}
      @*/
    public static boolean is_JML_Modifier(long mod)
    {
        return mod >= Modifier.MODEL.modifier;
    }
}
