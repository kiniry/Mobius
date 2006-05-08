package rcc;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.StringTokenizer;

import escjava.ast.TagConstants;
import escjava.translate.NoWarn;
import javafe.SrcToolOptions;
import javafe.util.Set;
import javafe.util.UsageError;


/**
 * @author rgrig
 */
public class RccOptions extends SrcToolOptions {

    // === Contruction ===
    
    public RccOptions() {
        super();
        // TODO Auto-generated constructor stub
    }
    
    
    // === Rcc options ===
    
    public boolean quiet        = false;
    public boolean wall         = false;
    public boolean noho         = false;  // ignore no holds
    public boolean agt          = false;  // add guarded_by this
    public boolean prg          = false;  // print redundant guards
    public boolean pjt          = false;  // print java w/ types
    public boolean pun          = false;  // print untriggered no_warns
    public boolean tse          = false;  // print stack trace on warning
    public boolean chl          = false;  // constructor holds locks
    public boolean dts          = false;  // default is thread_shared
    public boolean ihl          = false;  // initializer holds lock
    public boolean ihnl         = false;  // initializer holds lock
    public Set     ignoreAnnSet = null;
    public boolean stats        = false;
    public boolean plainWarning = false;
    public boolean suggest = false;       // suggest fixes (for wizard)
    public int     startLine = 0;
    
    
    // === Show functions ===
    
    public String showOptions(boolean all) {
        StringBuffer r = new StringBuffer(super.showOptions(all));
        r.append(" -pjt    print code with types\n");
        r.append(" -agt    assume unguarded shared fields guarded by this\n");
        r.append(" -prg    print redundant guards\n");
        r.append(" -noho   ignore no_hold's\n");
        r.append(" -wall   print all warnings\n");
        r.append(" -pun    print untriggered no_warn's / unneeded holds\n");
        r.append(" -chl    assume constructor holds self lock\n");
        r.append(" -dts    classes on command line are thread_shared by default\n");
        r.append(" -ihl    initializer blocks hold self/class lock\n");
        r.append(" -ihnl   static initializer blocks hold the null lock\n");
        r.append(" -quiet  don't print status messages\n");
        r.append("\n");
        r.append(" -nowarn <category>        turn off warning category\n");
        r.append(" -warn <category>          turn on warning category\n");    
        r.append(" -warn_package <package>   print warning from code in package\n");
        r.append(" -nowarn_package <package> turn off warnings from code in package\n");
        r.append(" -trace_error              for debugging\n");
        r.append(" -ignoreAnnFile <file>     ignore annotations at locs in file\n");
        r.append(" -suggest                  suggest fixes in warning messages\n");
        return r.toString();
    }
    
    public String showNonOptions() {
        return super.showNonOptions();
    }
    
    // === Process options ===
    /**
     * Process one option. 
     * (This interface is defined in <code>javafe.SrcToolOptions</code>)
     * 
     * @param option The option to be processed.
     * @param args   All options.
     * @param offset The index of the next option.
     * @return The index of the option to be processed on a subsequent call.
     * @throws UsageError When an option is recognized but badly formed
     *         (e.g., a parameter is missing).
     */
    public int processOption(String option, String[] args, int offset) throws UsageError {
        if (option.equals("-pjt")) {
            pjt = true;
            return offset;
        }
        if (option.equals("-ihl")) {
            ihl = true;
            return offset;
        }
        if (option.equals("-ihnl")) {
            ihnl = true;
            return offset;
        }
        if (option.equals("-prg")) {
            prg = true;
            return offset;
        }
        if (option.equals("-agt")) {
            agt = true;
            return offset;
        }
        if (option.equals("-noho")) {
            noho = true;
            return offset;
        }
        if (option.equals("-wall")) {
            wall = true;
            NoWarn.init();
            return offset;
        }
        if (option.equals("-pun")) {
            pun = true;
            return offset;
        }
        if (option.equals("-chl")) {
            chl = true;
            return offset;
        }
        if (option.equals("-dts")) {
            dts = true;
            return offset;
        }        
        if (option.equals("-suggest")) {
            suggest = true;
            return offset;
        }       
        if (option.equals("-trace_error")) {
            tse = true;
            return offset;
        }
        if (option.equals("-quiet")) {
            quiet = true;
            return offset;
        } else if (option.equals("-nowarn")) {
            assertArg(offset, args.length, "nowarn");
            setWarningStatus(args[offset], TagConstants.CHK_AS_ASSUME);
            return offset + 1;
        } else if (option.equals("-warn")) {
            assertArg(offset, args.length, "warn");
            setWarningStatus(args[offset], TagConstants.CHK_AS_ASSERT);
            return offset + 1;
        } else if (option.equals("-nowarn_package")) {
            assertArg(offset, args.length, "nowarn_package");
            //TODO: What happened to `package status'?
            //NoWarn.setPackageStatus(args[offset], TagConstants.CHK_AS_ASSUME);
            return offset + 1;
        } else if (option.equals("-warn_package")) {
            assertArg(offset, args.length, "warn_package");
            //TODO: What happened to `package status'?
            //NoWarn.setPackageStatus(args[offset], TagConstants.CHK_AS_ASSERT);
            return offset + 1;
        } else if (option.equals("-ignoreAnnFile")) {
            assertArg(offset, args.length, "ignoreAnnFile");
            ignoreAnnSet = new Set(readFile(args[offset]).elements());
            return offset + 1;
        }
        
        // Pass on unrecognized options.
        return super.processOption(option, args, offset);
    }

    /** Check that an option argument follows */
    private void assertArg(int off, int len, String opt) throws UsageError {
        if (off < len) return;
        throw new UsageError("Option " + opt + "expects an argument.");
    }
    
    /** Sets a warning status; reports if the name of the warning is invalid */
    private void setWarningStatus(String warn, int status) throws UsageError {
        int tag = NoWarn.toNoWarnTag(warn);
        if (tag == 0) {
            throw new UsageError("Invalid warning category: " + warn);
        }
        NoWarn.setChkStatus(tag, status);
    }

    /**
     * Makes a <code>Set</code>
     * whose elements are strings containing the first at most three (space 
     * separated) fields on each line of <code>filename</code>.
     * 
     * @param filename The file to read.
     * @return The set of strigns representing the first three fields on each line.
     * @throws RuntimeException If an IO error occurs.
     */
    private Set readFile(String filename) {
        try {
            FileInputStream fis = new FileInputStream(filename);
            InputStreamReader isr = new InputStreamReader(fis);
            BufferedReader br = new BufferedReader(isr);
            Set r =  new Set();
            
            String line = br.readLine();
            while (line != null) {
                StringTokenizer tok = new StringTokenizer(line);
                String element = null;
                for (int i = 0; i < 3 && tok.hasMoreTokens(); ++i) {
                    if (element == null) {
                        element = tok.nextToken();
                    } else {
                        element = element + " " + tok.nextToken();
                    }
                }
                if (element != null) {
                    r.add(element);
                }
                line = br.readLine();
            }
            
            return r;
        } catch(IOException e) {
          throw new RuntimeException("IOException: " + e);
        }
    }

    // === Local tests ===
    public static void main(String[] args) {
        // TODO Auto-generated method stub

    }

}

/** Boolean option */
class BO {
    
}

