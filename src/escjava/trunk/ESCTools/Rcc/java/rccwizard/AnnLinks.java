/* Copyright 2000, 2001, Compaq Computer Corporation */

package rccwizard;

/*
 * Change history:
 * 28 Sep 2000  flanagan           Created
 
 */

import java.util.Enumeration;
import java.util.Hashtable;
import java.io.ByteArrayOutputStream;

import javafe.ast.*;
import rcc.ast.*;
import rcc.ast.TagConstants;

import javafe.reader.StandardTypeReader;

import javafe.parser.PragmaParser;

import javafe.tc.TypeSig;
import javafe.tc.TypeCheck;

import javafe.util.*;


public class AnnLinks extends javafe.SrcTool {
    
    /** Our version number **/
    public final String version = "1.0.0, 6 dec 2000";
    
    
    /***************************************************
     *                                                 *
     * Generating an options message:                       *
     *                                                 *
     ***************************************************/
    
    /**
     ** Return the name of this tool.  E.g., "ls" or "cp".<p>
     **
     ** Used in usage and error messages.<p>
     **/
    public String name() { return "annotation linker"; }
    
    /**
     ** Print option option information to
     ** <code>System.err</code>. <p>
     **/
    public void showOptions() {
        super.showOptions();
        System.err.println("");
    }
    
    
    /***************************************************
     *                                                 *
     * Option processing:                               *
     *                                                 *
     ***************************************************/
    
    /**
     ** Process next tool option. <p>
     **
     ** See <code>Tool.processOption</code> for the complete
     ** specification of this routine.<p>
     **/
    public int processOption(String option, String[] args, int offset) {
        
        // Pass on unrecognized options:
        return super.processOption(option, args, offset);
    }
    
    
    /**
     ** This method is called on each <code>CompilationUnit</code>
     ** that this tool processes.  This method overrides the implementation
     ** given in the superclass, adding a couple of lines before the
     ** superclass implementation is called.
     **/
    public void handleCU(CompilationUnit cu) {
        //System.out.println ("handleCU"+cu );
        super.handleCU(cu);
    }
    
    /***************************************************
     *                                                 *
     *  Front-end setup: Use ESC stuff                       *
     *                                                 *
     ***************************************************/
    
    /**
     ** Returns the EscPragmaParser.
     **/
    public javafe.parser.PragmaParser makePragmaParser() {
        return new rcc.parser.RccPragmaParser();
    }
    
  
    
    /**
     ** Returns the pretty printer to set
     ** <code>PrettyPrint.inst</code> to.
     **/
    public PrettyPrint makePrettyPrint() {
        DelegatingPrettyPrint p = new RccPrettyPrint();
        p.del = new StandardPrettyPrint(p);
        return p;
    }
    
    /**
     ** Called to obtain an instance of the javafe.tc.TypeCheck class
     ** (or a subclass thereof). May not return <code>null</code>.  By
     ** default, returns <code>javafe.tc.TypeCheck</code>.
     **/
    public javafe.tc.TypeCheck makeTypeCheck() {
        return new rcc.tc.TypeCheck();
    }
    
    
    /***************************************************
     *                                                 *
     * Main processing code:                               *
     *                                                 *
     ***************************************************/
    
    /**
     ** Start up an instance of this tool using command-line arguments
     ** <code>args</code>. <p> 
     **
     ** This is the main entry point for the <code>rccjava</code>
     ** command.<p>
     **/
    //@ requires elemsnonnull(args)
    public static void main(String[] args) {
        //System.out.println ("main,"+args[2]);
        javafe.SrcTool t = new AnnLinks();
        t.run(args);
    }
    
    
    /***************************************************
     *                                                 *
     * SrcTool-instance specific processing:               *
     *                                                 *
     ***************************************************/
    
    /**
     ** This method is called by SrcTool on the TypeDecl of each
     ** outside type that SrcTool is to process. <p>
     **
     ** In addition, it calls itself recursively to handle types
     ** nested within outside types.<p>
     **/
    public void handleTD(TypeDecl td) {
        //System.out.println ("handleTD");
        
        TypeSig sig = TypeCheck.inst.getSig(td);
        sig.typecheck();
        
        AnnLinkVisitor v = new AnnLinkVisitor();
        td.accept(v);
    }
}

/** this visitor writes to stdout a table linking error locations to decl locations, 
 *  and decl locations to corresponding non_null annotations. 
 *
 *  Just does non_null on fields and parameters,
 *  and links from assignment statements to decl for rhs.
 */

class AnnLinkVisitor extends DefaultVisitor {
    
    public void visitModifierPragma(ModifierPragma x) {
        super.visitModifierPragma(x);
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        javafe.ast.PrettyPrint.inst.print(baos, 0, x);
        System.out.println("AnnText "+convert(x.getStartLoc())+" "+baos.toString());
    }

    
    public void visitTypeDecl(TypeDecl x) {
        super.visitTypeDecl(x);
        reportThreadLocalModifier(x);
        System.out.println("DeclName "+convert(x.getStartLoc())+" type "+x.id);
    }

    public void visitFieldDecl(FieldDecl x) {
        super.visitFieldDecl(x);
        if (!Modifiers.isStatic(x.modifiers)) {
            reportWarnDecl(x.getStartLoc(), x.parent.getStartLoc());
        }
    }
    
    private ModifierPragma searchModifierPragmas(ModifierPragmaVec x, String contains) {
        if( x != null ) {
            for(int i=0; i<x.size(); i++) {
                ModifierPragma mp = x.elementAt(i);
                ByteArrayOutputStream baos = new ByteArrayOutputStream();
                javafe.ast.PrettyPrint.inst.print(baos, 0, mp);
                if( baos.toString().indexOf(contains) >= 0 )
                    return mp;
            }
        }
        return null;    
    }
    
    private void reportThreadLocalModifier(TypeDecl x) {
        if( x.pmodifiers != null ) 
            for(int i=0; i<x.pmodifiers.size(); i++)
                visitModifierPragma(x.pmodifiers.elementAt(i));
        ModifierPragma mp = searchModifierPragmas(x.pmodifiers, "thread_local");
        if( mp != null ) {
            reportDeclAnn( x.getStartLoc(), mp.getStartLoc());
        }
    }

        
    private void reportWarnDecl(int locdecl, int locann) {
        if( locdecl != Location.NULL && !Location.isWholeFileLoc(locdecl) &&
            locann != Location.NULL && !Location.isWholeFileLoc(locann) ) {
            System.out.println("WarnDecl "+convert(locdecl)+" "+convert(locann));
        }
    }
    
    private void reportDeclAnn(int locdecl, int locann) {
        if( locdecl != Location.NULL && !Location.isWholeFileLoc(locdecl) &&
            locann != Location.NULL && !Location.isWholeFileLoc(locann) ) {
            System.out.println("DeclAnn "+convert(locdecl)+" "+convert(locann));
        }
    }
    
    private String convert(int loc) {
        return Location.toFileName(loc)+
            " "+Location.toLineNumber(loc)+
            " "+Location.toColumn(loc);
    }
}


