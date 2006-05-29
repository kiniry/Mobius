// @(#)$Id: TypeAttrib.java,v 1.19 2001/07/11 20:04:56 leavens Exp $

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
//import edu.iastate.cs.jml.checker.*;
import antlr.collections.AST;

public abstract class TypeAttrib implements /*LB Unifi,*/ JMLType {
  // methods from Subst class
    //LB  public Atype fromClass = null;
  public String packageName="";
  public String filename="";

  protected AST docComment = null;  

  public String getName () 
    {
	// this is a dummy default method so downcasting is unnecessary
	// in subclasses.
	return null;
    }
  
  public TypeAttrib getType () 
    {
	// this is a dummy default method so downcasting is unnecessary
	// in subclasses.
	return null;
    }

    /*LB  public Atype getFromClass ()
    {
	return fromClass;
    }

  public String getFromClassName ()
    {
      if (fromClass == null)
	 return "";
      else 
	 return fromClass.getName();
    }
    LB*/

  public String getPackageName ()
    {
      return packageName;
    }

  public void setPackageName (String cname)
    {
      packageName = cname;
    }
    /*LB
  public void setFromClass (Atype type)
    {
      fromClass = type;
    }

  public boolean equalAll (TypeAttrib t)
    {
      return false;
    }

  public SubstMap nullSubst() {
    return new IdentitySubstMap();
  }

  public SubstMap bindTo(LogicalVar lv1) {
    return new SubstMap(lv1, this);
  }

  public TypeAttrib apply(SubstMap s) {
    return this;
  }

  // methods from Unifi class

  public TypeAttrib toTerm(LogicalVar lv) {
    return new Avar(lv);
  }
  
  public boolean isVar() {
    return false;
  }

  public LogicalVar getVar() throws NotAVarException
  {
    throw new NotAVarException();
  }

  public JMLValueSequence subTerms ()
  {
    return (new JMLValueSequence());
  }

  public boolean sameKind (TypeAttrib t) {
    return false;
  }
LB*/
  // JMLType methods

  public abstract Object clone (); 

  public abstract boolean equals (Object o);

    /*LB
  public JMLValueSequence varsIn() {
        JMLValueSequence vs = new JMLValueSequence();
        if (isVar()) {
	  try {
		LogicalVar lv = (LogicalVar)getVar().clone();
		vs = vs.insertFront(lv);
	  } catch (NotAVarException e) {}
		return vs;
	} else { 
		JMLValueSequence vsTerms = this.subTerms();
		Enumeration e = vsTerms.elements();
		while (e.hasMoreElements()) 
		      vs = ((TypeAttrib)e.nextElement()).varsIn();
		return vs;
	}
  }

  public SubstMap MGU(TypeAttrib t) {
	int flag = 0;
	LogicalVar lv1, lv2;
	lv1 = null; lv2 = null;
	try {
	if (isVar() && t.isVar()) {
		flag = 1;
		lv1 = this.getVar();
		lv2 = t.getVar();
	}	
	if (isVar() && !t.isVar()) {
		flag = 2;
		lv1 = this.getVar();
	}	
	if (!isVar() && t.isVar()) {
		flag = 3;
		lv2 = t.getVar();
	}	
	if (!isVar() && !t.isVar())
		flag = 4;
	} catch (NotAVarException e) {
	     System.out.println("NotAVarException: "+e);
	}
	//System.out.println("flag " + flag);
	switch(flag) {
	case 1:
	  if (lv1.equals(lv2)) 
	    return this.nullSubst();
	  else 
	    return (this.toTerm(lv2)).bindTo(lv1);
	case 2: 
	  //System.out.println("In here");
	  // System.out.println("length3 " + t.varsIn().length());
	  if (!(t.varsIn()).has(lv1))
	    return t.bindTo(lv1);
	  else
	    return null;
	case 3:
	  if (!(this.varsIn()).has(lv2))
	    return this.bindTo(lv2);
	  else 
	    return null;
	case 4:
	  //System.out.println("In here 1");
	  if (this.sameKind(t))
	    return Typing.listUnify(this.subTerms(),t.subTerms());
	  return null;
	default: 
	  return null;
	}
  }		       

  public Adec getAllEnv (Adec env, int phase)
    {
      return new Adec (new Api ());
    }
    LB*/
  public String toString()
  { return "this is the base class typeattrib!"; }

  public void print()
  { System.out.println( "this is the base class typeattrib"); }

  /** is it legal to assign type t to the type represented by this? **/
    /*LB
  public boolean isAssignable (TypeAttrib t, int context, Adec env)
    {
      return this.equals(t);
    }

  public int getLevel (TypeAttrib t2)
    {
      if (this.equals(t2))
	return 1;
      else
	return -1;
    }
    LB*/
    public void setDocCommentAST(AST d)
    {
	docComment = d;
    }

    public AST getDocCommentAST()
    {
	return docComment;
    }

}













