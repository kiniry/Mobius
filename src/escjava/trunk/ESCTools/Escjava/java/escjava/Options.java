/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;
import java.io.*;

import javafe.ast.*;
import javafe.util.Set;
import javafe.util.UsageError;
import escjava.ast.*;
import escjava.ast.TagConstants;
import escjava.translate.NoWarn;

/**
 * This class parses the options on the command-line and is a structure for holding
 * the values of options.
 */

public class Options extends javafe.SrcToolOptions
{
    // Global escjava flags

    /*
     * These are set by the command-line switches of the same name.
     * They default to false (unset).
     */

    public boolean suggest = false;

    public boolean pjt    = false; // print java w/ types
    public boolean nvu    = false;
    public boolean pgc    = false;
    public boolean pdsa    = false;
    public boolean pcc    = false;
    // a pruned, pretty printed version of pcc:
    public boolean counterexample = false;
    public boolean stats = false;
    public boolean plainWarning = false;

    /** Statically check against redundant specs?  Default is true. */
    public boolean checkRedundantSpecs = true;

    // trace info: (0) no, (1) default, (2) verbose
    public int traceInfo = 1;
    //@ invariant 0 <= traceInfo && traceInfo < 3;

    /** When set, pretty-prints the VCs that are obtained with verbose output
	or in the log (-sxLog) */
    public boolean prettyPrintVC = false;

    /** When set, prints out the desugared specs for debugging purposes. */
    public boolean desugaredSpecs = false;

    /** When true, no variable output (e.g. execution time) is printed,
     so that output can be compared to an oracle output file.
     */
    public boolean testMode = false;

    /** When true, pretty prints each compilation unit on the command-line;
     this is only used for testing, to test the combining of refinements.
     */
    public boolean testRef = false;

    /** Temporary option to turn on purity checking, since it is off by
	default until purity issues with inheritance are resolved.
    */
    public boolean checkPurity = false;

    /** When true, parses pragmas that begin with /*+@, which are normally
     parsed only by JML; this allows test runs in which everything JML
     parses is parsed by escjava, to see if we have full coverage of all
     of JML.
     */
    public boolean parsePlus = false;

    /** When true, does not print any warnings about things not checked. */
    public boolean noNotCheckedWarnings = false;

    public boolean spvc = true;
    public boolean dsa = true;
    //@ invariant spvc ==> dsa  // spvc requires dsa for soundness
    public boolean passify = false;
    public boolean wpp = false;
    public boolean useDefpred = false;
    public int wpnxw = 0;
    public int namePCsize = 0;

    public boolean peepOptE=true;
    public boolean peepOptGC=true;
    public boolean lazySubst = false;
    public boolean mergeInv=false;

    public boolean useAllInvPostCall = false;
    public boolean useAllInvPostBody = false;
    public boolean useAllInvPreBody = false;
    public boolean allocUseOpt = true;

    public static final int LOOP_FAST = 0;
    public static final int LOOP_SAFE = 1;
    public static final int LOOP_FALL_THRU = 2;
    public int loopTranslation = LOOP_FAST;
    //@ invariant LOOP_FAST <= loopTranslation && loopTranslation <= LOOP_FALL_THRU;

    // The default loop unrolling is: -loop 1.5 
    public int loopUnrollCount = 1;
    public boolean loopUnrollHalf = true;

    public boolean preciseTargets = false;

    public boolean predAbstract = false;
    public boolean inferPredicates = false;

    public boolean noDirectTargetsOpt = false;
    public boolean nestQuantifiers = false;

    public boolean lastVarUseOpt = true;
    public boolean noVarCheckDeclsAndUses = false;

    public boolean useIntQuantAntecedents = false;

    public boolean excuseNullInitializers = false;

    /** The following values are used: <br>
     *   0-never, 1-atomic (default), 2-always
     */
    public int strongAssertPost = 1;

    public boolean showCallDetails = true;
    public boolean showLoopDetails = false;
    public boolean bubbleNotDown=false;
    public int startLine = -1;    // starting line # for processing
    public int vclimit = 500000;

    public boolean noOutCalls = false;

    // flags primarily used by Houdini
    public boolean printAssumers = false;
    public boolean noPeepOptGCAssertFalse = false;
    public boolean assertContinue = false;
    public boolean trackReadChars = true;
    public boolean guardedVC = false;
    public String guardedVCDir;
    public String guardedVCFileNumbers = "files.txt";
    public String guardedVCGuardFile = "guards.txt";
    public String guardedVCPrefix = "G_";
    public String guardedVCFileExt = "sx";
    public Set guardVars = new Set();  
    public String ClassVCPrefix = "*Class*";
    public String MethodVCPrefix = "*Method*";

    public Set ignoreAnnSet = null;

    public boolean printCompilationUnitsOnLoad = false;

    // filter invariants and axioms
    public boolean filterInvariants = false;
    
    // filter method specifications
    public boolean filterMethodSpecs = false;

    public Set routinesToCheck = null;  // null means "check everything"
    public Set routinesToSkip = null;  // null means "skip nothing"

    // do the inlined constructor experiment?
    public boolean inlineConstructors = false;
    
    // do some other inlining experiment, using at least one of the two
    // inline depth flags?
    public boolean inlineDepthFlags = false;
    
    // when checking a constructor of a class T, inline every call
    // this.m(...) transitively from within the constructor, whenever m
    // statically resolves to a non-overridable instance method defined in T.
    public boolean inlineFromConstructors = false;

    public String sxLog = null;

    // The following switch hardcodes whether or not also_requires is to
    // be part of the annotation language
    public boolean allowAlsoRequires = true;

    /**
     * Number of stages to run.  The stages currently in order are:
     *     1. loading, parsing, and type checking
     *     2. generating the type-specific background predicate
     *        3. translating from Java to GC
     *        4. translating from GC to DSA
     *     5. generating the VC from the GC
     *     6. calling the theorem prover to verify the VC<p>
     *
     * defaults to running all stages (6); must be positive.<p>
     *
     * -nocheck sets <code>stages</code> to run all but the last
     * stage (5).  The -stages option can be used to set
     * <code>stages</code> to a particular value.<p>
     */
    public int stages    = 6;


    //* Which file to obtain the universal background predicate from.
    public String univBackPredFile = null;

 
    // Generating an options message

    /**
     * Print option option information to
     * <code>System.err</code>. <p>
     */
    public String showOptions(boolean all) {
        String s = super.showOptions(all);
        /* Note:  The following should list all of the "public" options, not
         * debugging options that are present only in experimental versions
         * at SRC.
         */
         // FIXME - pretty print these, with explanation
        s += "  -counterexample -loopSafe -loop <iterCount>[.0|.5] -nocheck" + eol;
        s += "  -noredundancy -notrace -nowarn <category> -plainwarning"+eol;
        s += "  -routine <routineId> -routine <fullyQualifiedRoutineSignature>"+eol;
        s += "  -routineIndirect <routineFile> -start <line#> -suggest" + eol;
        s += "  -vclimit <n> -warn <category>" + eol;
        if (all) {
            // FIXME - add in the experimental options
        }
        return s;
    }


    // Option processing

    /**
     * Process next tool option.
     *
     * <p> See {@link javafe.Options#processOption(String [])} for the complete
     * specification of this routine.
     */
    public int processOption(String option, String[] args, int offset) 
		throws UsageError {
        if (option.equals("-nocheck")) {
            stages = 5;        // run all but last stage
            return offset;
        } else if (option.equals("-stages")) {
            if (offset == args.length) {
                throw new UsageError("Option " + option +
                                     " requires one integer argument");
            }
            try {
                stages = new Integer(args[offset]).intValue();
		if (stages<1)
                        throw new NumberFormatException();
            } catch (NumberFormatException e) {
                throw new UsageError("Option " + option +
		     " requires one positive integer argument: " + 
                     e.toString());
            }
            return offset+1;
        } else if (option.equals("-start")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option +
                                     " requires one integer argument");
            }
            try {
                startLine = new Integer(args[offset]).intValue();
            } catch (NumberFormatException e) {
                throw new UsageError("Option " + option +
		     " requires one positive integer argument: " + 
                     e.toString());
            }
            return offset+1;
        } else if (option.equals("-vclimit")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option +
                                     " requires one integer argument");
            }
            try {
                vclimit = new Integer(args[offset]).intValue();
            } catch (NumberFormatException e) {
                throw new UsageError("Option " + option +
		     " requires one positive integer argument: " + 
                     e.toString());
            }
            return offset+1;
        } else if (option.equals("-inlineFromConstructors")) {
                inlineFromConstructors = true;
                return offset;
        } else if (option.equals("-inlineCheckDepth")) {
            inlineDepthFlags = true;
            // can't use this along with the -inlineConstructors flag
            if (inlineConstructors)
                throw new UsageError("Can't use -inlineConstructors in combination with either -inlineCheckDepth or -inlineDepthPastCheck");
            if (offset == args.length) {
                throw new UsageError("Option " + option +
                                     " requires one integer argument");
            }
            try {
                Main.gctranslator.inlineCheckDepth =
                    new Integer(args[offset]).intValue();
                if (Main.gctranslator.inlineCheckDepth < 0)
                    throw new NumberFormatException();
            } catch (NumberFormatException e) {
                throw new UsageError("Option " + option +
		     " requires one positive integer argument: " + 
                     e.toString());
            }
            return offset+1;
        } else if (option.equals("-inlineDepthPastCheck")) {
            inlineDepthFlags = true;
            // can't use this along with the -inlineConstructors flag
            if (inlineConstructors)
                throw new UsageError("can't use -inlineConstructors in combination with either -inlineCheckDepth or -inlineDepthPastCheck");
            if (offset == args.length) {
                throw new UsageError("Option " + option +
                                     " requires one integer argument");
            }
            try {
                Main.gctranslator.inlineDepthPastCheck =
                    new Integer(args[offset]).intValue();
                if (Main.gctranslator.inlineDepthPastCheck < 0)
                    throw new NumberFormatException();
            } catch (NumberFormatException e) {
                throw new UsageError("Option " + option +
		     " requires one positive integer argument: " + 
                     e.toString());
            }
            return offset+1;
        } else if (option.equals("-inlineConstructors")) {
            // can't use this along with either of the inline depth flags
            if (inlineDepthFlags)
		throw new UsageError("can't use -inlineConstructors in combination with either -inlineCheckDepth or -inlineDepthPastCheck");
            inlineConstructors = true;
            return offset;
        } else if (option.equals("-suggest")) {
            suggest = true;
            return offset;
        } else if (option.equals("-pgc")) {
            pgc = true;
            return offset;
        } else if (option.equals("-pcc")) {
            pcc = true;
            return offset;
        } else if (option.equals("-nospvc")) {
	    spvc = false;
	    return offset;
        } else if (option.equals("-passify")) {
	    passify = true;
	    return offset;
        } else if (option.equals("-wpp")) {
	    wpp = true;
	    return offset;
        } else if (option.equals("-useDefpred")) {
            useDefpred = true;
            return offset;
        } else if (option.equals("-nodsa")) {
            dsa = false;
            spvc = false;  // spvc requires dsa for soundness
            return offset;
        } else if (option.equals("-pdsa")) {
            pdsa = true;
            return offset;
        } else if (option.equals("-wpnxw")) {
            if (offset >= args.length) {
                throw new UsageError("Option " + option +
                                     " requires one integer argument");
            }
            wpnxw = new Integer(args[offset]).intValue();
            return offset+1;
    
        } else if (option.equals("-namePCsize")) {
            if (offset >= args.length) {
                throw new UsageError("Option " + option +
                                     " requires one integer argument");
            }
            namePCsize = new Integer(args[offset]).intValue();
            return offset+1;
        } else if (option.equals("-stats")) {
            stats = true;
            return offset;
        } else if (option.equals("-pjt")) {
            pjt = true;
            return offset;
        } else if (option.equals("-nvu")) {
            nvu = true;
            return offset;
        } else if (option.equals("-assertContinue")) {
            assertContinue = true;
            return offset;
        } else if (option.equals("-noTrackReadChars")) {
            trackReadChars = false;
            return offset;
        } else if (option.equals("-filterMethodSpecs")) {
            filterMethodSpecs = true;
            return offset;
        } else if (option.equals("-noPeepOptGCAssertFalse")) {
            noPeepOptGCAssertFalse = true;
            return offset;
        } else if (option.equals("-noEpeepopt")) {
            peepOptE = false;
            return offset;
        } else if (option.equals("-noGCpeepopt")) {
            peepOptGC = false;
            return offset;
        } else if (option.equals("-lazySubst")) {
            lazySubst = true;
            return offset;
        } else if (option.equals("-mergeinv")) {
            mergeInv = true;
            return offset;
        } else if (option.equals("-noAllocUseOpt")) {
            allocUseOpt = false;
            return offset;
        } else if (option.equals("-useAllInvPostCall")) {
            useAllInvPostCall = true;
            return offset;
        } else if (option.equals("-useAllInvPostBody")) {
            useAllInvPostBody = true;
            return offset;
        } else if (option.equals("-useAllInvPreBody")) {
            useAllInvPreBody = true;
            return offset;
        } else if (option.equals("-filterInvariants")) {
            filterInvariants = true;
            return offset;
        } else if (option.equals("-printAssumers")) {
            printAssumers = true;
            return offset;
        } else if (option.equals("-printCompilationUnitsOnLoad")) {
            printCompilationUnitsOnLoad = true;
            return offset;
        } else if (option.equals("-guardedVC")) {
            if (offset >= args.length) {
                throw new UsageError("Option " + option +
                                     " requires one directory argument");
            }
            guardedVC = true;
	    guardedVCDir = args[offset];
            return offset+1;
        } else if (option.equals("-ignoreAnnFile")) {
            if (offset >= args.length) {
                throw new UsageError("Option " + option +
                                     " requires one filename argument");
            }
            ignoreAnnSet = new Set(readFile(args[offset]).elements());
            // System.out.println("Ignore set: "+ignoreAnnSet+"\n");
            return offset+1;
        } else if (option.equals("-routine")) {
	    // the argument to "-routine" is either a simple routine name or a fully
	    // qualified routine name with signature, but we won't ever parse these
	    if (offset == args.length) {
                throw new UsageError("Option " + option +
                                     " requires one argument");
	    }
	    String routine = args[offset].intern();
	    if (routinesToCheck == null) {
		routinesToCheck = new Set();
	    }
	    routinesToCheck.add(routine);
	    return offset+1;
        } else if (option.equals("-skip")) {
	    // the argument to "-skip" is either a simple routine name or a fully
	    // qualified routine name with signature, but we won't ever parse these
	    if (offset == args.length) {
                throw new UsageError("Option " + option +
                                     " requires one argument");
	    }
	    String routine = args[offset].intern();
	    if (routinesToSkip == null) {
		routinesToSkip = new Set();
	    }
	    routinesToSkip.add(routine);
	    return offset+1;
        } else if (option.equals("-routineIndirect")) {
	    if (offset == args.length) {
                throw new UsageError("Option " + option +
                                     " requires one argument");
	    }
	    if (routinesToCheck == null) {
		routinesToCheck = new Set();
	    }
	    String routineIndirectionFilename = args[offset];
	    try {
		BufferedReader in = new BufferedReader(
				   new FileReader(routineIndirectionFilename));
		while (true) {
		    String routine = in.readLine();
		    if (routine == null) {
			break;
		    }
		    routine = routine.intern();
		    routinesToCheck.add(routine);
		}
	    } catch (IOException e) {
		throw new UsageError("error reading routine indirection file '" +
			       routineIndirectionFilename + "': " +
			       e.toString());
	    }
	    return offset+1;
        } else if (option.equals("-loopSafe")) {
	    loopTranslation = LOOP_SAFE;
            return offset;
        } else if (option.equals("-preciseTargets")) {
            preciseTargets = true;
            loopTranslation = LOOP_SAFE;
            return offset;
        } else if (option.equals("-loop")) {
            // syntax:  -loop <N>[.0|.5]
            if (offset == args.length) {
                throw new UsageError("Option " + option +
                                     " requires one argument");
	    }
	    String number = args[offset];
	    if (number.length() == 0 || option.charAt(0) == '.') {
		throw new UsageError("illegal argument to -loop: " + number);
	    }
	    // any other parsing error will be caught in the following loop
	    int cnt = 0;
	    boolean andAHalf = false;
	    for (int i = 0; i < number.length(); i++) {
		char ch = number.charAt(i);
		if ('0' <= ch && ch <= '9') {
		    if (10000 <= cnt) {
			throw new UsageError("-loop specifies too many iterations: " +
				       number);
		    }
		    cnt = 10*cnt + ch - '0';
		    continue;
		} else if (ch == '.') {
		    if (number.length() == i+2) {
			if (number.charAt(i+1) == '5') {
			    andAHalf = true;
			    break;
			} else if (number.charAt(i+1) == '0') {
			    andAHalf = false;
			    break;
			}
		    }
		}
		throw new UsageError("illegal argument to -loop: " + number);
	    }
	    loopUnrollCount = cnt;
	    loopUnrollHalf = andAHalf;
	    return offset+1;
        } else if (option.equals("-loopFallThru")) {
            loopTranslation = LOOP_FALL_THRU;
            return offset;
        } else if (option.equals("-predAbstract")) {
            predAbstract = true;
            loopTranslation = LOOP_SAFE;
            lastVarUseOpt = false;
            return offset;
        } else if (option.equals("-inferPredicates")) {
            inferPredicates = true;
            predAbstract = true;
            loopTranslation = LOOP_SAFE;
            lastVarUseOpt = false;
            return offset;
        } else if (option.equals("-noDirectTargetsOpt")) {
            noDirectTargetsOpt = true;
            return offset;
        } else if (option.equals("-nestQuantifiers")) {
            nestQuantifiers = true;
            return offset;
        } else if (option.equals("-useIntQuantAntecedents")) {
            useIntQuantAntecedents = true;
            return offset;
        } else if (option.equals("-excuseNullInitializers")) {
            excuseNullInitializers = true;
            return offset;
        } else if (option.equals("-strongAssertPostNever")) {
            strongAssertPost = 0;
            return offset;
        } else if (option.equals("-strongAssertPostAtomic")) {
            strongAssertPost = 1;
            return offset;
        } else if (option.equals("-strongAssertPostAlways")) {
            strongAssertPost = 2;
            return offset;
        } else if (option.equals("-noLastVarUseOpt")) {
            lastVarUseOpt = false;
            return offset;
        } else if (option.equals("-noVarCheckDeclsAndUses")) {
            noVarCheckDeclsAndUses = true;
            return offset;
        } else if (option.equals("-hidecall")) {
            showCallDetails = false;
            return offset;
        } else if (option.equals("-showloop")) {
            showLoopDetails = true;
            return offset;
        } else if (option.equals("-plainwarning")) {
            plainWarning = true;
            return offset;
        } else if (option.equals("-noredundancy")) {
            checkRedundantSpecs = false;
            return offset;
        } else if (option.equals("-notrace")) {
            traceInfo = 0;
            return offset;
        } else if (option.equals("-verboseTrace")) {
            traceInfo = 2;
            return offset;
        } else if (option.equals("-counterexample")) {
            counterexample = true;
            return offset;
        } else if (option.equals("-bubbleNotDown")) {
	    bubbleNotDown = true;
	    return offset;
        } else if (option.equals("-noOutCalls")) {
	    noOutCalls = true;
	    return offset;
        } else if (option.equals("-backpredfile")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option +
                                     " requires one argument");
            }
            univBackPredFile = args[offset];
            return offset+1;
        } else if (option.equals("-sxLog")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option +
                                     " requires one argument");
            }
            sxLog = args[offset];
            return offset+1;
        } else if (option.equals("-nowarn")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option +
                                     " requires one argument");
            }
            if (args[offset].equals("All")) {
		NoWarn.setAllChkStatus(TagConstants.CHK_AS_ASSUME);
            } else {
		int tag = NoWarn.toNoWarnTag(args[offset]);
		if (tag==0) {
		    throw new UsageError("'" + args[offset]
				   + "' is not a legal warning category");
		}
		NoWarn.setChkStatus(tag, TagConstants.CHK_AS_ASSUME);
            }
            return offset+1;
        } else if (option.equals("-warn")) {
            if (offset>=args.length) {
                throw new UsageError("Option " + option +
                                     " requires one argument");
            }
            // Note:  There's an intentional lack of symmetry with -nowarn
            // here, in that "-warn All" is not supported.  This design
            // allows ESC/Java to include special checks, perhaps like the
            // Stale checks of the Higher-Level Races checker, that won't
            // be publicly advertised.
            int tag = NoWarn.toNoWarnTag(args[offset]);
            if (tag==0) {
                throw new UsageError("'" + args[offset]
                           + "' is not a legal warning category");
            }
            NoWarn.setChkStatus(tag, TagConstants.CHK_AS_ASSERT);
            return offset+1;
        } else if (option.equals("-parsePlus")) {
            parsePlus = true;
            return offset;
        } else if (option.equals("-noNotCheckedWarnings")) {
            noNotCheckedWarnings = true;
            return offset;
        } else if (option.equals("-testMode")) {
            testMode = true;
            return offset;
        } else if (option.equals("-testRef")) {
            testRef = true;
            return offset;
	} else if (option.equals("-checkPurity")) {
	    checkPurity = true;
	    return offset;
	} else if (option.equals("-ppvc") | option.equals("-prettyPrintVC")) {
	    prettyPrintVC = true;
	    return offset;
	} else if (option.equals("-showDesugaredSpecs")) {
	    desugaredSpecs = true;
	    return offset;
        }
    
        // Pass on unrecognized options:
        return super.processOption(option, args, offset);
    }


    private Vector readFile(String filename) {
        Vector r = new Vector();
        StringBuffer s = new StringBuffer();
        try {
            Reader R = new BufferedReader(new InputStreamReader(new FileInputStream(filename)));
            int c;
            do {
                while( (c=R.read())!= -1 && c != '\n' ) {
                    s.append( (char)c );
                }
                // Delete from 3rd space on
                String st = s.toString();
                int i=st.indexOf(' ');
                if( i != -1 ) i=st.indexOf(' ',i+1);
                if( i != -1 ) i=st.indexOf(' ',i+1);
                if( i != -1 ) st=st.substring(0,i);
                r.addElement( st );
                s.setLength(0);
            } while( c != -1 );
            return r;
        } catch(IOException e) {
            throw new RuntimeException("IOException: " + e);
        }
    }
} // end of class Options

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 85
 * End:
 */

