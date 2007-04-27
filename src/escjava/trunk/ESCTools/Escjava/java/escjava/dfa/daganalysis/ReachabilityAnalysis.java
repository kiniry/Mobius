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
    
    private static long constructTime = 0;
    private static long getNodesTime = 0;
    private static long spTime = 0;
    private static long proverTime = 0;

    // the control flow graph and all its nodes
    private CFD graph;
    private Set graphNodes;

    // strongest postconditions
    private Map spOfNode;

    private String assertLabel(GuardedCmd gc) {
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
        Enumeration c = n.getChildren().elements();
        while (c.hasMoreElements())
            collectNodes(c.nextElement());
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
        Expr sp = (Expr) spOfNode.get(n);
        if (sp != null) return sp;

        // compute precondition for [n] as a disjunction of its preconditions
        Enumeration p = n.getParents().elements();
        Expr pre = GC.falselit;
        while (p.hasMoreElements()) 
            pre = GC.or(pre, spDfs(p.nextElement()));

        // compute the sp
        Expr post = n.computeSp(pre);

        // return and cache
        spOfNode.put(n, post);
        return post;
    }

    private void internalAnalyze(GuardedCmd gc) {
        // construct the graph, assumming that gc doesn't contain VARIN
        constructTime = System.currentTimeMillis();
        GCtoCFDBuilder builder = new GCtoCFDBuilder();
        graph = builder.constructGraph(gc, null);
        if (graph.isEmpty()) return; // nothing to check
        constructTime = System.currentTimeMillis() - constructTime;

        // DBG
        //System.out.println("Constructed graph: " + graph);
        graph.printStats();
         
        // do DFS
        getNodesTime = System.currentTimeMillis();
        spOfNode = new HashMap();
        graphNodes = new HashSet();
        collectNodes(graph.getInitNode());
        getNodesTime = System.currentTimeMillis() - getNodesTime;

        // set the initial node always reachable
        spTime = System.currentTimeMillis();
        spOfNode.put(graph.getInitNode(), (Expr) GC.truelit);
        Iterator nodes = graphNodes.iterator();
        while (nodes.hasNext()) spDfs((Node)nodes.next());
        spTime = System.currentTimeMillis() - spTime;
        
        // check whether the exit code has an unsatisfiable postcondition
        proverTime = System.currentTimeMillis();
        Expr spOfExit = (Expr)spOfNode.get(graph.getExitNode());
        if (Simplifier.isFalse(spOfExit))
            ErrorSet.error("The method never terminates.");
        proverTime = System.currentTimeMillis() - proverTime;
        
        // report times
        System.err.println("construct_time " + constructTime);
        System.err.println("get_nodes_time " + getNodesTime);
        System.err.println("sp_time " + spTime);
        System.err.println("prover_time " + proverTime);
    }
    
    private static final String POST_WARN =
        "The assumptions are inconsistent, the method might not terminate, or the analysis is imprecise.";
    private static final String CODE_WARN = "Code not checked.";
    private static final String ASSERT_WARN = "Assertion not checked."; 

    /**
     * Reports errors for unchecked code, unchecked assertions, and unchecked
     * postconditions. The location is not reported for postconditions.
     * We do not report @unreachable as being unreached. We skip
     * labels with no location information.
     */
    private void reportUnreachableLabel(LabelData ld) {
        String suffix = " (" + ld.getMsgShort() + ")";
        int loc = LabelDataUtil.getLocation(ld);
        
        if (loc == Location.NULL) return;
        
        switch (ld.getMsgTag()) {
        case TagConstants.CHKCODEREACHABILITY:
            return; // the user wants this to be unreachable so don't report
        case TagConstants.CHKPOSTCONDITION:
        case TagConstants.CHKUNEXPECTEDEXCEPTION:
        case TagConstants.CHKUNEXPECTEDEXCEPTION2:
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
