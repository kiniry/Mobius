// @(#)$Id: ModifierSet.java,v 1.9 2001/02/22 02:59:00 leavens Exp $

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

//import edu.iastate.cs.jml.models.*;

/** a set of modifiers
 *  @author Clyde Ruby and Gary T. Leavens
 **/
public /*@ pure @*/ class ModifierSet implements JMLType
{

    //@ public model JMLObjectSet theModifiers;
    /*@ public invariant theModifiers != null
      @           && (\forall Object o; theModifiers.has(o);
      @                                 o instanceof Modifier);
      @*/

    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	protected final long modifierSet;

    //@ protected invariant modifierSet >= 0;

    //@ protected depends theModifiers <- modifierSet;
    /*@ protected represents theModifiers \such_that
      @                   (\forall Modifier m; ;
      @                            theModifiers.has(m)
      @                            <==> (modifierSet & m.getModifier() != 0));
      @*/

    /*@  public normal_behavior
      @    assignable theModifiers;
      @    ensures theModifiers.isEmpty();
      @*/
    public ModifierSet()
    {
        modifierSet = 0;
    }

    /*@  public normal_behavior
      @    requires mod != null;
      @    assignable theModifiers;
      @    ensures theModifiers.size() == 1 && theModifiers.has(mod);
      @*/
    public ModifierSet(Modifier mod)
    {
        if (mod != null) {
            modifierSet = mod.getModifier();
        } else {
            modifierSet = 0;
        }
    }

    //@ assignable theModifiers;
    protected ModifierSet(long m)
    {
        modifierSet = m;
    }

    /*@  public normal_behavior
      @    requires mod != null;
      @    ensures \result.theModifiers.equals(
      @                this.theModifiers.union(new JMLObjectSet(mod)));
      @    ensures_redundantly \result.theModifiers.has(mod);
      @*/
    public ModifierSet insert(Modifier mod)
    {
        if (mod != null) {
            return (new ModifierSet(modifierSet | mod.getModifier()));
        } else {
            return this;
        }
    }

    /*@  public normal_behavior
      @    requires mod != null;
      @    ensures \result <==> theModifiers.has(mod);
      @   also
      @    requires mod == null;
      @    ensures \result == false;
      @*/
    public boolean has(Modifier mod)
    {
        if (mod != null) {
            return (modifierSet & mod.getModifier()) != 0;
        } else {
            return false;
        }
    }

    /*@  public normal_behavior
      @    ensures \result <==> theModifiers.isEmpty();
      @*/
    public boolean isEmpty()
    {
        return (modifierSet == 0);
    }

    /*@  public normal_behavior
      @    requires mods != null;
      @    ensures \result.theModifiers.equals(
      @                this.theModifiers.union(mods.theModifiers));
      @*/
    public ModifierSet union(ModifierSet mods)
    {
        if (mods != null) {
            return (new ModifierSet(modifierSet | mods.modifierSet));
        } else {
            return this;
        }
    }

    /*@  public normal_behavior
      @    requires mods != null;
      @    ensures \result.theModifiers.equals(
      @                this.theModifiers.intersection(mods.theModifiers));
      @*/
    public ModifierSet intersection(ModifierSet mods)
    {
        if (mods != null) {
            return (new ModifierSet(modifierSet & mods.modifierSet));
        } else {
            return this;
        }
    }

    /*@  public normal_behavior
      @    requires mods != null;
      @    ensures \result <==>
      @               !(new ModifierSet().equals(
      @                   this.theModifiers.intersection(mods.theModifiers)));
      @*/
    public boolean intersects(ModifierSet mods)
    {
        if (mods != null) {
            return (modifierSet & mods.modifierSet) != 0;
        } else {
            return false;
        }
    }

    /*@  public normal_behavior
      @    requires mods != null;
      @    ensures \result.theModifiers.equals(
      @                this.theModifiers.difference(mods.theModifiers));
      @*/
    public ModifierSet difference(ModifierSet mods)
    {
        if (mods != null) {
            return (new ModifierSet(modifierSet & (~mods.modifierSet) ));
        } else {
            return this;
        }
    }

    /*@  public normal_behavior
      @    requires mods != null;
      @    ensures \result.theModifiers.equals(
      @                union(this.difference(mods),
      @                      mods.difference(this)));
      @*/
    public ModifierSet symmetricDiff(ModifierSet mods)
    {
        if (mods != null) {
            long diff1 = (modifierSet & ~mods.modifierSet);
            long diff2 = (~modifierSet & mods.modifierSet);
            return (new ModifierSet(diff1 | diff2));
        } else {
            return this;
        }
    }

    /*@ also
      @  public normal_behavior
      @    requires o instanceof ModifierSet;
      @    ensures \result
      @           <==> this.theModifiers.equals(((ModifierSet)o).theModifiers);
      @   also
      @    requires !(o instanceof ModifierSet);
      @    ensures \result == false;
      @*/
    public boolean equals (Object o)
    {
        if (o instanceof ModifierSet) {
            return (modifierSet == ((ModifierSet)o).modifierSet);
        } else {
            return false;
        }
    }

    /*@  public normal_behavior
      @    ensures \result == theModifiers.size();
      @*/
    public int size()
    {
        int sz = 0;
      
        long mod = 0x0001;
        int i=1; 
        while (i<Modifier.meaning.length && mod != 0) {
            if ((modifierSet & mod) != 0) {
                sz++;
            }
            mod = mod << 1;
            i++;
        }
        return sz;
    }

    /*@ also
      @  public normal_behavior
      @    ensures \result == this;
      @*/
    public Object clone ()
    {
        return this;
    }

    /*@ also
      @  public normal_behavior
      @    ensures (* \result is a string representation of this *);
      @*/
    public String toString()
    {
        // want to not print out "(default privacy)", so start at 2!
        int i=2;   
        long mod = 0x0002; // 2**(2-1) = 2
        String blank = "";
        String newStr = "";
        while (i<Modifier.meaning.length && mod != 0) {
            if ((modifierSet & mod) != 0) {
                newStr += blank + Modifier.meaning[i];
                blank = " ";
            }
            mod = mod << 1;
            i++;
        }
        return newStr;
    }

    /*@ also
      @  public normal_behavior
      @    ensures \result != null
      @         && (* \result is a string representation of this,
      @               which includes JML comment markers for
      @               JML modifiers, if in_JML_comment is false *);
      @*/
    public String toString(boolean in_JML_comment)
    {
        // want to not print out "(default privacy)", so start at 2!
        int i=2;   
        long mod = 0x0002; // 2**(2-1) = 2
        String blank = "";
        String newStr = "";
        while (i<Modifier.meaning.length && mod != 0) {
            if ((modifierSet & mod) != 0) {
                newStr += blank;
                if (in_JML_comment || !(Modifier.is_JML_Modifier(mod))) {
                    newStr += Modifier.meaning[i];
                } else {
                    newStr += "/*@ " + Modifier.meaning[i] + " @*/";
                }
                blank = " ";
            }
            mod = mod << 1;
            i++;
        }
        return newStr;
    }

    /*@  public normal_behavior
      @    ensures \result <==> toString().isEmpty();
      @*/
    public boolean printsEmpty()
    {
        return (modifierSet < 2);
    }

    /*@  public normal_behavior
      @    ensures \result <==>
      @           theModifiers.has(Modifier.MODEL)
      @        || theModifiers.has(Modifier.GHOST);
      @*/
    public boolean isModelOrGhost()
    {
        return has(Modifier.MODEL) || has(Modifier.GHOST);
    }

    public static void main(String [] argv)
    {
        ModifierSet ms = new ModifierSet();
        ModifierSet p = new ModifierSet(Modifier.PUBLIC);
        ModifierSet s = new ModifierSet(Modifier.STATIC);
        ModifierSet m = new ModifierSet(new Modifier("model"));
        ms = ms.union(p).union(s).union(m);
        System.out.println("public prints as '" + p + "'");
        System.out.println("public static model prints as '" + ms + "'");
    }

}
