/* Copyright 2000, 2001, Compaq Computer Corporation */


package javafe.ast;

import java.io.OutputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import javafe.util.Assert;
import javafe.util.Location;

public class DelegatingPrettyPrint extends PrettyPrint {
  
  //@ invariant del!=null
  public PrettyPrint del;
  
  // Caller must establish del!=null!
  //@ requires false
  protected DelegatingPrettyPrint() { }
  
  //@ requires del!=null
  //@ requires self!=null
  protected DelegatingPrettyPrint(PrettyPrint self, PrettyPrint del) { 
    super(self); 
    this.del = del; 
  }
  
  public void print(OutputStream o, CompilationUnit cu) {
    del.print(o, cu);
  }
  
  public void printnoln(OutputStream o, int ind, TypeDecl d) {
    del.printnoln(o, ind, d);
  }
  
  public void print(OutputStream o, int ind, Stmt s) {
    del.print(o, ind, s);
  }
  
  public void print(OutputStream o, int ind, TypeDeclElem d, 
		    Identifier classId, boolean showBody) {
    del.print(o, ind, d, classId, showBody);
  }
  
  public void print(OutputStream o, TypeNameVec tns) {
    del.print(o, tns);
  }
  
  public void print(OutputStream o, int ind, FormalParaDeclVec fps) {
    del.print(o, ind, fps);
  }
  
  public void print(OutputStream o, int ind, ExprVec es) {
    del.print(o, ind, es);
  }
  
  public void print(OutputStream o, GenericVarDecl d) {
    del.print(o, d);
  }
  
  public void print(OutputStream o, int ind, LocalVarDecl d,
		    boolean showBody) {
    del.print(o, ind, d, showBody);
  }
  
  public void print(OutputStream o, int ind, FieldDecl d, boolean showBody) {
    del.print(o, ind, d, showBody);
  }
  
  public void print(OutputStream o, Type t) {
    del.print(o, t);
  }
  
  public void print(OutputStream o, Name n) {
    del.print(o, n);
  }
  
  public void print(OutputStream o, int ind, VarInit e) {
    del.print(o, ind, e);
  }
  
  public void print(OutputStream o, int ind, ObjectDesignator od) {
    del.print(o, ind, od);
  }
  
  public void print(OutputStream o, LexicalPragma lp) {
    del.print(o, lp);
  }
  
  public void print(OutputStream o, int ind, TypeDeclElemPragma tp) {
    del.print(o, ind, tp);
  }
  
  public void print(OutputStream o, int ind, ModifierPragma mp) {
    del.print(o, ind, mp);
  }
  
  public void print(OutputStream o, int ind, StmtPragma sp) {
    del.print(o, ind, sp);
  }
  
  public void print(OutputStream o, int ind, TypeModifierPragma tp) {
    del.print(o, ind, tp);
  }
  
  public String toString(int tag) {
    return del.toString(tag);
  }
}




