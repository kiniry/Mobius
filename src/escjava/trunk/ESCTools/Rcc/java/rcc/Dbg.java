/**
 * Copyright (c) 2005, TopCoder Inc. All rights reserved.
 */
package rcc;

import java.io.PrintStream;

import javafe.ast.ExprVec;
import javafe.ast.FieldDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.GenericVarDecl;
import javafe.ast.LocalVarDecl;
import javafe.ast.Name;
import javafe.ast.ObjectDesignator;
import javafe.ast.PrettyPrint;
import javafe.ast.Type;
import javafe.ast.TypeNameVec;
import javafe.ast.VarInit;


/** 
 * We use <code>NullPrintStream.out</code> below to turn off all
 * debugging output that uses the class <code>Dbg</code>.
 */
class NullPrintStream extends PrintStream {
    private NullPrintStream() {
        super(System.out); // strange that I have to do this
    }
    public static NullPrintStream out = new NullPrintStream();
    public void println(String s) {
        // do nothing
    }
}

/**
 * Helper functions for doing debug.
 * Currently it only includes convenient methods for dumping AST nodes
 * with an optional tag.
 */
public class Dbg {
    private static final PrintStream out = NullPrintStream.out;
    //private static final PrintStream out = System.err;

    public static void o(TypeNameVec a) { o("", a); }
    public static void o(FormalParaDeclVec a) { o("", a); }
    public static void o(ExprVec a) { o("", a); }
    public static void o(GenericVarDecl a) { o("", a); }
    public static void o(Type a) { o("", a); }
    public static void o(Name a) { o("", a); }
    public static void o(VarInit a) { o("", a); }
    public static void o(ObjectDesignator a) { o("", a); }
    public static void o(LocalVarDecl a) { o("", a); }
    public static void o(FieldDecl a) { o("", a); }
    
    public static void o(String t, TypeNameVec a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    public static void o(String t, FormalParaDeclVec a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    public static void o(String t, ExprVec a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    public static void o(String t, GenericVarDecl a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    public static void o(String t, Type a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    public static void o(String t, Name a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    public static void o(String t, VarInit a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    public static void o(String t, ObjectDesignator a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    
    public static void o(String t, LocalVarDecl a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
    public static void o(String t, FieldDecl a) { out.println(t + ": " + PrettyPrint.inst.toString(a)); }
}
