package escjava.dfa.daganalysis;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import java.util.List;
import java.util.Map.Entry;

import escjava.ast.EscPrettyPrint;
import escjava.ast.ExprCmd;
import escjava.ast.GuardedCmd;
import escjava.ast.LabelExpr;
import escjava.ast.TagConstants;
import escjava.dfa.buildcfd.GCtoCFDBuilder;
import escjava.dfa.cfd.CFD;
import escjava.dfa.cfd.CodeNode;
import escjava.dfa.cfd.Node;
import escjava.dfa.cfd.NodeList.Enumeration;
import escjava.translate.ErrorMsg;
import escjava.translate.GC;
import escjava.translate.LabelData;

import javafe.ast.Expr;
import javafe.ast.PrettyPrint;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Location;

/**
 * Used to sort labels such as those corresponding to postcondition
 * checks come first and otherwise are sorted by file line number;
 * also helps to extract a location---the most significant one---
 * from the label.
 * 
 * @author mikolas rgrig
 */
class LabelDataUtil implements Comparator {
    
    /** Extract most significant location. */
    static public int getLocation(LabelData ld) {
        if (ld.hasUseLoc()) {
            return ld.getUseLoc();
        } else if (ld.hasDeclLoc()) {
            return ld.getDeclLoc();
        }
        Assert.fail("We expect that each label has a location.");
        // If you are really sure you want label without location within ESC/Java
        // then for this class it should be fine if you just remove the assertion above.
        return Location.NULL;
    }
    
    public int compare(Object ao, Object bo) {
        LabelData a = (LabelData)ao;
        LabelData b = (LabelData)bo;
        int locA = getLocation(a);
        int locB = getLocation(b);
        int lineA = Location.toLineNumber(locA);
        int lineB = Location.toLineNumber(locB);
        int tagA = a.getMsgTag();
        int tagB = b.getMsgTag();
        boolean postA = isPost(tagA); 
        boolean postB = isPost(tagB);
        
        if (postA && postB) return tagA - tagB;
        if (postA != postB) return postA ? -1 : +1;
        if (lineA != lineB) return lineA - lineB;
        if (locA != locB) return locA - locB;
        if (tagA != tagB) return tagA - tagB;
        Assert.fail("Hmm? This is strange: same error at the same location?");
        return -1;
    }
    
    /** Tags from (exceptional) postconditions. */
    private static final int[] POST_TAGS = {
        TagConstants.CHKPOSTCONDITION,
        TagConstants.CHKUNEXPECTEDEXCEPTION,
        TagConstants.CHKUNEXPECTEDEXCEPTION2
    };
    private static boolean isPost(int tag) {
        int i;
        for (i = 0; i < POST_TAGS.length && tag != POST_TAGS[i]; ++i);
        return i < POST_TAGS.length;
    }
}


/**
 * Finds commands that are unreachable. Example:
 * <tt>
 *   if (x > 1) {
 *     // ... code that does not modify x ... 
 *     if (x <= 1) {
 *       // unreachable code
 *     }
 *   }
 * </tt>
 * 
 * TODO: make it parametrizable so it uses SP or WP according to the command line options.
 * Right now it uses SP (which is the default in escjava).
 */
public class ReachabilityAnalysis {

    // The (acyclic) control flow diagram/graph we analyze.
    private CFD graph;

    private Set graphNodes;

    // Maps processed nodes to their postcondition
    private Map cache;

    // Map of reported errort to a boolean detemining whether that error is ever
    // checked
    Map reportErrors;

    String assertLabel(GuardedCmd gc) {
        if (gc.getTag() == TagConstants.ASSERTCMD) {
            ExprCmd ec = (ExprCmd) gc;
            Expr e = ec.pred;
            if (e.getTag() == TagConstants.LABELEXPR) {

                LabelExpr le = (LabelExpr) e;
                String label = le.label.toString();

                return label;
            }
        }
        return null;
    }

    // Adds all nodes reachable from [n] (children) to [graphNodes].
    private void collectNodes(Node n) {
        if (graphNodes.contains(n))
            return;
        graphNodes.add(n);

        String label = getLabel(n);
        if (label != null)
            reportErrors.put(label, new Boolean(false));

        Enumeration c = n.getChildren().elements();
        while (c.hasMoreElements()) {
            collectNodes(c.nextElement());
        }
    }

    String getLabel(Node n) {
        if (n instanceof CodeNode) {
            CodeNode cn = (CodeNode) n;
            String label = assertLabel(cn.getCode());
            return label;
        }

        return null;
    }

    // Compute the strongest postcondition (SP) of [n].
    private Expr spDfs(Node n) {
        Expr sp = (Expr) cache.get(n);
        if (sp != null)
            return sp;

        // compute precondition for [n] as a conjuction of its preconditions
        Enumeration p = n.getParents().elements();
        Expr pre = GC.falselit;
        while (p.hasMoreElements()) {
            pre = GC.or(pre, spDfs(p.nextElement()));
        }

        // compute the sp
        Expr post = n.computeSp(pre);

        // System.out.println("Checking postcondition for the node: " + n);

        // check if false

        boolean isCodeNode = n instanceof CodeNode;

        boolean isFalse;
        boolean runProver;

        // TODO: see how this can be done nicer
        // Runs the prover only when at least one of the node's parent 
        // doesn't have the identity SP transformer
        if (isCodeNode) {
            boolean allParentsIdentity = true;
            for (Enumeration en = n.getParents().elements(); en
                    .hasMoreElements();) {
                Node parent = en.nextElement();
                if (parent instanceof CodeNode) // TODO: bleh!
                    allParentsIdentity = false;
            }

            runProver = n.getParents().getCount() == 0 || !allParentsIdentity;
        } else {
            runProver = true;
        }
        

        // testing what happend if prover ran only in non-chain nodes
//        if ((n.getChildren().getCount() == 1) && (n.getParents().getCount() == 1) ) 
//            runProver = false;
        
        if (runProver) {
            isFalse = Simplifier.isFalse(pre);
        } else {
            // if we're not running the prover, we just check for the false literal
            isFalse = GC.isFalse(pre);
        }

        if (isFalse) {
            if (isCodeNode) {
                System.out.print("*** Code:  ");

                ((EscPrettyPrint) PrettyPrint.inst).print(System.out, 0,
                        ((CodeNode) n).getCode());

                System.out.println("    is unreachable.");
            }

            post = GC.falselit; // pass on the result 
        } else {
            if (isCodeNode) {
                String label = getLabel(n);
                if (label != null) {
                    Assert
                            .notFalse(reportErrors.containsKey(label),
                                    "This label should have been included in the hash map during node collection.");
                    reportErrors.put(label, new Boolean(true)); // mark label as
                    // reachable
                }
            }
        }

        // return and cache
        cache.put(n, post);
        return post;
    }

    private void internalAnalyze(GuardedCmd gc) {
        // DBG
//        System.out.println("\n**** Analysing Guarded Command:");
//        ((EscPrettyPrint) PrettyPrint.inst).print(System.out, 0, gc);
//        System.out.println("");

        // construct the graph
        GCtoCFDBuilder builder = new GCtoCFDBuilder();
        graph = builder.constructGraph(gc, null); // assumes gc does not
                                                    // contain VARIN command

        if (graph.isEmpty()) { // TODO: make this nicer
            System.err.println("Empty graph!!");
            return;
        }

        List unreachable = builder.getUnreachable();

        // TODO: collect labels from these as well:
        for (Iterator it = unreachable.iterator(); it.hasNext();) {
            CFD c = (CFD) it.next();
//            System.out.println("Unreachable:" + c);
        }
        
        // DBG
         System.out.println("Constructed graph: " + graph);
         graph.printStats();
         
         
        // do DFS
        reportErrors = new HashMap();
        graphNodes = new HashSet();
        collectNodes(graph.getInitNode());
        cache = new HashMap();

        // set the initial node always reachable
        cache.put(graph.getInitNode(), (Expr) GC.truelit);
        Iterator nodes = graphNodes.iterator();
        while (nodes.hasNext()) {
            spDfs((Node) nodes.next());
        }

        // collect (and sort) the labels that were never reached
        Set unreachedLabels = new TreeSet(new LabelDataUtil());
        for (Iterator it = reportErrors.entrySet().iterator(); it.hasNext();) {
            Entry e = (Entry) it.next();
            String label = (String) e.getKey();
            boolean checked = ((Boolean) e.getValue()).booleanValue();
            if (!checked) {
                unreachedLabels.add(LabelData.parse(label));
            }
        }
        
        // report errors
        for (Iterator it = unreachedLabels.iterator(); it.hasNext();) {
            reportUnreachableLabel((LabelData)it.next());
        }
    }
    
    private static final String POST_WARN =
        "The assumptions are inconsistent, the method might not terminate, or the analysis is imprecise.";
    private static final String CODE_WARN = "Code not checked.";
    private static final String ASSERT_WARN = "Assertion not checked."; 

    /**
     * Reports errors for unchecked code, unchecked assertions, and unchecked
     * postconditions. The location is not reported for postconditions.
     * We do not report @unreachable as being unreached. We also skip
     * labels with no location information---just for robustness.
     * 
     * TODO: We might want to not report exceptionals postconditions
     *       because we think that means the postcondition is already reported.
     */
    private void reportUnreachableLabel(LabelData ld) {
        String suffix = " (" + ld.getMsgShort() + ")";
        int loc = LabelDataUtil.getLocation(ld);
        
        // robustness check
        if (loc == Location.NULL) return;
        
        switch (ld.getMsgTag()) {
        case TagConstants.CHKCODEREACHABILITY:
            return; // the user wants this to be unreachable so don't report
        case TagConstants.CHKPOSTCONDITION:
        case TagConstants.CHKUNEXPECTEDEXCEPTION:  // TODO: check this is really for exsures
        case TagConstants.CHKUNEXPECTEDEXCEPTION2: // TODO: check this is really for exsures
            ErrorSet.warning(POST_WARN + suffix);
            break;
        case TagConstants.CHKASSERT:
        case TagConstants.CHKEXPRDEFINEDNESS:
        case TagConstants.CHKEXPRDEFNORMPOST:
        case TagConstants.CHKEXPRDEFEXCEPOST:
            ErrorSet.warning(loc, ASSERT_WARN + suffix);
            break;
        default:
            // we assume it's code (for now)
            ErrorSet.warning(loc, CODE_WARN + suffix);
        }
    }

    // pre: gc does not contain VARIN commands
    public static void analyze(GuardedCmd gc) {
        new ReachabilityAnalysis().internalAnalyze(gc);
    }
}
