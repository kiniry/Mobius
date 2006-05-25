package rccwizard;

//import escjava.ast.TagConstants;
//import escjava.translate.NoWarn;
import javafe.SrcToolOptions;
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
    
    
    // === RccWizard options ===
    
    public static boolean pmnr       = false;  //  public methods have no requires
    public static boolean readonly   = false;  //  only insert readonly annot.
    public static boolean guessnull  = true; 
    
    
    // === Show functions ===
    
    public String showOptions(boolean all) {
        StringBuffer r = new StringBuffer(super.showOptions(all));
        r.append("-pmnr          public methods cannot have requires clauses\n");
        r.append("-noguessnull   don't guess null as guarding lock\n");
        r.append("-readonly      only guess readonly annotations\n");
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
     */
    public int processOption(String option, String[] args, int offset) throws UsageError {
        if (option.equals("-pmnr")) {
            pmnr = true;
            return offset;
        } else if (option.equals("-readonly")) {
            readonly = true;
            return offset;
        } else if (option.equals("-noguessnull")) {
            guessnull = false;
            return offset;
        }
        return super.processOption(option, args, offset);
    }


    // === Local tests ===
    public static void main(String[] args) {
        // TODO Auto-generated method stub

    }

}

