/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe;


import java.util.Vector;

import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.*;

import java.util.StringTokenizer;
import java.util.Hashtable;
import java.util.ArrayList;
import java.util.Iterator;

public class CopyLoaded extends FrontEndTool implements Listener {

    public String name() { return "CopyLoaded"; }

    private PrintWriter libIndirectWriter;
    private PrintWriter progIndirectWriter;

    /* 
     * This maps files from original progIndirect file names to their names 
     * relative to the outDir
     */
    public final Vector progIndirectFiles = new Vector();
    //@ invariant progIndirectFiles.elementType == \type(String);
    //@ invariant progIndirectFiles.owner == this;
    //@ invariant !progIndirectFiles.containsNull;

    public final Vector argumentFileNames = new Vector();
    //@ invariant argumentFileNames.elementType == \type(String);
    //@ invariant !argumentFileNames.containsNull;
    //@ invariant argumentFileNames.owner == this;



    /***************************************************
     *                                                 *
     * Keeping track of loaded CompilationUnits:       *
     *                                                 *
     **************************************************/


    //@ invariant loaded != null;
    //@ invariant loaded.elementType == \type(CompilationUnit);
    //@ invariant !loaded.containsNull;
    //@ invariant loaded.owner == this;
    public Vector loaded = new Vector();

    //@ invariant loaded != argumentFileNames;
 
    public CopyLoaded() {
        //@ set argumentFileNames.elementType = \type(String);
        //@ set argumentFileNames.containsNull = false;
        //@ set argumentFileNames.owner = this;
    
        //@ set loaded.elementType = \type(CompilationUnit);
        //@ set loaded.containsNull = false;
        //@ set loaded.owner = this;
    
        //@ set progIndirectFiles.containsNull = false;
        //@ set progIndirectFiles.elementType = \type(String);
        //@ set progIndirectFiles.owner = this;
    }


    public void setup() { 
        super.setup();
    }


    private String packageDirForFile(/*@ non_null */ CompilationUnit cu) {
        Name pkg = cu.pkgName;
        String s = pkg == null ? "" : pkg.printName() + ".";
        s = s.replace('.', '/'); 
        return s;
    }

    public void notify(CompilationUnit justLoaded) {
        loaded.addElement(justLoaded);
     
        String fileName = Location.toFileName(justLoaded.loc);
        /* if a Java file, then copy the file over into outDir */
        if (fileName.endsWith(".java")) {
            copySourceFile(fileName, 
                   packageDirForFile(justLoaded) + fileNameName(fileName));
        } else {
            TypeDeclVec elems = justLoaded.elems;
            /* generate a spec file for each type decl in compilation unit */
            for (int i=0; i<elems.size(); i++) {
                TypeDecl d = elems.elementAt(i);
                TypeSig sig = TypeCheck.inst.getSig(d);
                if (d.specOnly || d.isBinary()) {
                    printSpec(sig.toString());
                }
            }
        }
    }

    /***************************************************
     *                                                 *
     * Main processing code:                   *
     *                                                 *
     **************************************************/



    //@ requires \nonnullelements(args);
    public static void main(String[] args) {
        Tool t = new CopyLoaded();
        int result = t.run(args);
        if (result != 0) System.exit(result);
    }
    
    public Options makeOptions() {
        return new CopyLoadedOptions();
    }
    
    public CopyLoadedOptions options() {
        return (CopyLoadedOptions)options;
    }



    //@ ensures \nonnullelements(\result);
    //@ ensures \result != null;
    public String[] FQNpackage(/*@ non_null */ String s) {
        StringTokenizer st = new StringTokenizer(s, ".", false);
        int len = st.countTokens();
        return fillArray(st, len-1);
    } 

    //@ ensures \result != null;
    public String FQNname(/*@ non_null */ String s) {
         return s.substring(s.lastIndexOf(".") + 1);
    } 
 
    //@ ensures \nonnullelements(\result);
    //@ ensures \result != null;
    public String[] fileNamePackage(/*@ non_null */ String file) {
        StringTokenizer st = new StringTokenizer(file, "/", false);
        int len = st.countTokens();
        return fillArray(st, len-1);
    } 


    //@ ensures \result != null;
    public String fileNameName(/*@ non_null */ String s) {
         return s.substring(s.lastIndexOf("/") + 1);
    }    

    //@ ensures \nonnullelements(\result);
    //@ ensures \result != null;
    public String[] directoryPackage(/*@ non_null */ String dir) {
        StringTokenizer st = new StringTokenizer(dir, "/", false);
        int len = st.countTokens();
        return fillArray(st, len);
    } 

    //@ ensures \nonnullelements(\result);
    //@ ensures \result != null;
    private String[] fillArray(/*@ non_null */ StringTokenizer st, int len) {
        if (len < 0) {
            return new String[0];
        }
        String array[] = new String[len];
        for (int i = 0; i < len; i++) {
            array[i] = st.nextToken();
        }
        return array;
    }    



    //@ requires \nonnullelements(P);
    private String makeDirTree(/*@ non_null */ String root, 
                   /*@ non_null */ String P[]) {
        String s = root;
        for (int i = 0; i < P.length; i++) {
            s = s + "/" + P[i];
            java.io.File f = new File(s);
            if (!f.exists()) {
                System.out.println("[making " + s + "]");
                f.mkdir();            
            } else {
            }
        }
        return s;
    }




    //@ requires \nonnullelements(P);
    //@ ensures \result != null;
    private String makeDirPath(/*@ non_null */ String P[]) {
        String s = "";
        for (int i = 0; i < P.length; i++) {
            s = s + P[i] +"/";
        }
        return s;
    }

    /**
     * Prints the spec file for the FQN s.  The file is written
     * relative to the outDir.
     */  
    public void printSpec(/*@ non_null */ String s) {
        String P[] = FQNpackage(s);
        String T = FQNname(s);
        TypeSig sig = OutsideEnv.lookup(P, T);
        Assert.notFalse(sig != null); //@ nowarn Pre
    
        String path = makeDirTree(options().outDir, P);
        String outFile = T + ".spec";
        String filename = path + "/" +  outFile;
    
        System.out.println("[generating spec file for " + s + 
                           " as " + filename + "]");
    
        //@ assume libIndirectWriter != null;
        libIndirectWriter.println("./" + makeDirPath(P) + outFile);
    
        FileOutputStream fos = null;
        try {
            fos = new FileOutputStream(filename);
        } catch (Exception e) {
            ErrorSet.fatal(e.getMessage());
        }
        PrettyPrint.inst.print(fos, sig.getCompilationUnit());
    }

    public final void frontEndToolProcessing(ArrayList args) {
        /*
         * At this point, all options have already been processed and
         * the front end has been initialized.
         */
    
        String outDir = options().outDir;
        String outProgIndirect = options().outProgIndirect;
        String outLibIndirect = options().outLibIndirect;
        
        System.out.println("[outdir is " + outDir + "]");
    
        // Set up to receive CompilationUnit-loading notification events:
        OutsideEnv.setListener(this);
    
        // create the outDir
        if (outDir.startsWith(".")) {
            makeDirTree(".", directoryPackage(outDir));
        } else {
            makeDirTree("", directoryPackage(outDir));
        } 
        
        // set up the indirection files.
        try {
            progIndirectWriter =
            new PrintWriter(new FileWriter(new File(outProgIndirect)));
            libIndirectWriter = 
            new PrintWriter(new FileWriter(new File(outLibIndirect)));
        } catch (IOException e) {
            ErrorSet.fatal(e.getMessage());
        }
    
        /*
         * Load in each source file:
         */
	Iterator i = args.iterator();
	while (i.hasNext()) OutsideEnv.addSource((String)i.next());
    
         /* load in source files from supplied file name */
	i = argumentFileNames.iterator();
	while (i.hasNext()) {
            String argumentFileName = (String)i.next();
             try {
                 BufferedReader in = new BufferedReader(
                             new FileReader(argumentFileName));
                 String s;
                 while ((s = in.readLine()) != null) {
                    // allow blank lines in files list
                    if (!s.equals("")) {
                    progIndirectFiles.addElement(s);
                    OutsideEnv.addSource(s); 
                    }
                }
             } catch (IOException e) {
		ErrorSet.fatal(e.getMessage());
             }
         }
    
	i = loaded.iterator();
	while (i.hasNext()) {
            handleCU((CompilationUnit)i.next());
        }
    
        progIndirectWriter.close();
        libIndirectWriter.close();
    }


    /**
     * Copy the source file original into the file newName.  newName
     * is appended to the outDir to construct the full file location
     * of the new file.  This method also puts the newName into the
     * correct indirection file.
     */
    private void copySourceFile(/*@ non_null */ String original, 
                /*@ non_null */ String newName) {
        try {
            String path = makeDirTree(options().outDir, fileNamePackage(newName));
            String newFileName = path + "/" + fileNameName(newName);
    
            System.out.println("[copying source file " + original + 
                       " to " + newFileName + "]");
    
            //@ assume libIndirectWriter != null;
            //@ assume progIndirectWriter != null;
            if (progIndirectFiles.contains(original)) {
                progIndirectWriter.println("./" + newName);
            } else {
                libIndirectWriter.println("./" + newName);
            }
            
            File f = new File(newFileName);
            BufferedReader reader = new BufferedReader(new FileReader(original));
            PrintWriter writer = new PrintWriter(new FileWriter(f));
            String s;
            while ((s = reader.readLine()) != null) {
                writer.println(s);
            }
            writer.close();
        } catch (IOException e) {
            ErrorSet.fatal(e.getMessage());
        }
    }


    /**
     * Process each CU's type decls.
     */
    public void handleCU(/*@ non_null */ CompilationUnit cu) {
        // Iterate over all the TypeDecls representing outside types in cu:
        TypeDeclVec elems = cu.elems;
        for (int i=0; i<elems.size(); i++) {
            TypeDecl d = elems.elementAt(i);
            handleTD(d);
        }
    }

    /**
     * Called from handleCU on each TypeDecl from the CU's loaded from the
     * program files.  In addition, it calls itself recursively to handle types
     * nested within outside types.<p>
     */
    public void handleTD(/*@ non_null */ TypeDecl td) {
        TypeSig sig = TypeCheck.inst.getSig(td);
        if (sig.getTypeDecl().specOnly)    // do not process specs
            return;
        
        System.out.println("\n" + sig.toString() + " ...");
        
                    // Do actual work:
        boolean aborted = processTD(td);
        
        TypeDecl decl = sig.getTypeDecl();
        for (int i=0; i<decl.elems.size(); i++) {
            if (decl.elems.elementAt(i) instanceof TypeDecl)
            handleTD((TypeDecl)decl.elems.elementAt(i)); //@ nowarn Cast
        }
    }
    
    
    /**
     * Typecheck a TypeDecl;
     * return true if we had to abort. <p>
     *
     * Precondition: td is not from a binary file.<p>
     */
    private boolean processTD(/*@ non_null */ TypeDecl td) {
        int errorCount = ErrorSet.errors;
        TypeSig sig = TypeCheck.inst.getSig(td);
        sig.typecheck();
    
        return false;
    }
    

}

class CopyLoadedOptions extends SrcToolOptions {

    /*@ non_null */ public String outDir = "./outdir/src-annotated";
    /*@ non_null */ public String outProgIndirect = "./outProgIndirect";
    /*@ non_null */ public String outLibIndirect = "./outLibIndirect";

   
    public String showNonOptions() {
        return ("<program indirection file>");
    }

    public String showOptions(boolean all) {
        StringBuffer sb = new StringBuffer(super.showOptions(all));
        sb.append("  -outdir <root of output files>"); sb.append(eol);
        sb.append("  -outProgIndirect <new prog Indirect file>");sb.append(eol);
        sb.append("  -outLibIndirect <new lib Indirect file>"); sb.append(eol);
        sb.append("  -f <file containing source file names>"); sb.append(eol);
        return sb.toString();
    }


    /***************************************************
     *                                                 *
     * Option processing:                   *
     *                                                 *
     **************************************************/

    private final String name = "CopyLoaded";
    
    public int processOption(String option, String[] args, int offset) 
                                        throws UsageError {
        if (option.equals("-outProgIndirect")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option + 
                                         " requires one argument");
            }
            outProgIndirect = args[offset];
            return offset + 1;
        } else if (option.equals("-outLibIndirect")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option + 
                                         " requires one argument");
            }
            outLibIndirect = args[offset];
            return offset + 1;
        } else if (option.equals("-outdir")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option + 
                                         " requires one argument");
            }
            outDir = args[offset];
            return offset + 1;
        } else {
            // Pass on unrecognized options:
            return super.processOption(option, args, offset);
        }
    }
}
