/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import javafe.util.Assert;
import javafe.util.Location;
import javafe.util.ErrorSet;


// Convention: unless otherwise noted, integer fields named "loc" refer
// to the location of the first character of the syntactic unit


/* ---------------------------------------------------------------------- */

/** The <code>make</code> method of this class has the side effect of
pointing the <code>parent</code> pointers of the <code>TypeDecl</code>s
inside a <code>CompilationUnit</code> to point to that unit. */

public class CompilationUnit extends ASTNode {
  public Name pkgName;

  public LexicalPragmaVec lexicalPragmas;

  public /*@non_null*/ ImportDeclVec imports;

  public /*@non_null*/ TypeDeclVec elems;

  //@ invariant loc!=javafe.util.Location.NULL
  public int loc;


  private void postCheck() {
    for(int i = 0; i < elems.size(); i++) {
      for(int j = i+1; j < elems.size(); j++)
	Assert.notFalse(elems.elementAt(i) != elems.elementAt(j));  //@ nowarn Pre
    }
  }

    /**
     ** Return true iff this CompilationUnit was created from a .class
     ** file.
     **/
    public boolean isBinary() {
	return Location.toFileName(loc).endsWith(".class");
    }

  public int getStartLoc() { return loc; }
  public int getEndLoc() { 
    if (elems==null || elems.size()<1)
      return super.getEndLoc();

    return elems.elementAt(elems.size()-1).getEndLoc();
  }


// Generated boilerplate constructors:

  /**
   ** Construct a raw CompilationUnit whose class invariant(s) have not
   ** yet been established.  It is the caller's job to
   ** initialize the returned node's fields so that any
   ** class invariants hold.
   **/
  //@ requires I_will_establish_invariants_afterwards
  protected CompilationUnit() {}    //@ nowarn Invariant,NonNullInit


// Generated boilerplate methods:

  public final int childCount() {
     int sz = 0;
     if (this.lexicalPragmas != null) sz += this.lexicalPragmas.size();
     if (this.imports != null) sz += this.imports.size();
     if (this.elems != null) sz += this.elems.size();
     return sz + 1;
  }

  public final Object childAt(int index) {
          /*throws IndexOutOfBoundsException*/
     if (index < 0)
        throw new IndexOutOfBoundsException("AST child index " + index);
     int indexPre = index;

     int sz;

     if (index == 0) return this.pkgName;
     else index--;

     sz = (this.lexicalPragmas == null ? 0 : this.lexicalPragmas.size());
     if (0 <= index && index < sz)
        return this.lexicalPragmas.elementAt(index);
     else index -= sz;

     sz = (this.imports == null ? 0 : this.imports.size());
     if (0 <= index && index < sz)
        return this.imports.elementAt(index);
     else index -= sz;

     sz = (this.elems == null ? 0 : this.elems.size());
     if (0 <= index && index < sz)
        return this.elems.elementAt(index);
     else index -= sz;

     throw new IndexOutOfBoundsException("AST child index " + indexPre);
  }   //@ nowarn Exception

  public final String toString() {
     return "[CompilationUnit"
        + " pkgName = " + this.pkgName
        + " lexicalPragmas = " + this.lexicalPragmas
        + " imports = " + this.imports
        + " elems = " + this.elems
        + " loc = " + this.loc
        + "]";
  }

  public final int getTag() {
     return TagConstants.COMPILATIONUNIT;
  }

  public final void accept(Visitor v) { v.visitCompilationUnit(this); }

  public final Object accept(VisitorArgResult v, Object o) {return v.visitCompilationUnit(this, o); }

  public void check() {
     super.check();
     if (this.pkgName != null)
        this.pkgName.check();
     if (this.lexicalPragmas != null)
        for(int i = 0; i < this.lexicalPragmas.size(); i++)
           this.lexicalPragmas.elementAt(i).check();
     for(int i = 0; i < this.imports.size(); i++)
        this.imports.elementAt(i).check();
     if (this.elems == null) throw new RuntimeException();
     postCheck();
  }

  //@ requires loc!=javafe.util.Location.NULL
  //@ ensures \result!=null
  public static CompilationUnit make(Name pkgName, LexicalPragmaVec lexicalPragmas, /*@non_null*/ ImportDeclVec imports, /*@non_null*/ TypeDeclVec elems, int loc) {
     //@ set I_will_establish_invariants_afterwards = true
     CompilationUnit result = new CompilationUnit();
     result.pkgName = pkgName;
     result.lexicalPragmas = lexicalPragmas;
     result.imports = imports;
     result.elems = elems;
     result.loc = loc;
     return result;
  }
}
