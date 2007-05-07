package escjava.dfa.daganalysis;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import javafe.ast.Expr;
import javafe.ast.ExprVec;
import javafe.ast.VariableAccess;
import javafe.util.Assert;
import javafe.util.ErrorSet;
import javafe.util.Location;
import escjava.ast.ExprCmd;
import escjava.ast.GuardedCmd;
import escjava.ast.LabelExpr;
import escjava.ast.NaryExpr;
import escjava.ast.TagConstants;
import escjava.dfa.buildcfd.GCtoCFDBuilder;
import escjava.dfa.cfd.CFD;
import escjava.dfa.cfd.CodeNode;
import escjava.dfa.cfd.Node;
import escjava.dfa.cfd.NodeList.Enumeration;
import escjava.translate.GC;
import escjava.translate.LabelData;
import escjava.translate.VcToString;

/**
 * Used to sort labels such as those corresponding to postcondition
 * checks come first and otherwise are sorted by file line number;
 * also helps to extract a location---the most significant one---
 * from the label.
 * 
 * TODO: All these labels look horrible. Why both LabelData and ints? etc.
 * TODO: Make static all methods that can be statics so that |this| is
 *       not carried around.
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

/** A simple structure to associate label information to nodes. */
class NodeAndLabel {
    public Node node;
    public LabelData ld;
    public int loc;
    public NodeAndLabel(Node n) {
        node = n;
        ld = null;
        loc = Location.NULL;
    }
    public NodeAndLabel(Node n, String label) {
        Assert.notFalse(label != null);
        ld = LabelData.parse(label);
        loc = LabelDataUtil.getLocation(ld);
        node = n;
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
 */
public class ReachabilityAnalysis {
    // the control flow graph, its nodes, and those we are interested in
    private CFD graph;
    private HashSet graphNodes;

    // strongest postconditions
    private Map spOfNode;
    
    
    /*
     * The DAG-to-tree transformation. Tree is an euphemism because only
     * sharing that shrinks the size of the printed version is eliminated.
     * 
     * We maintain three maps
     *   dag -> var -> tree -> size
     * of type
     *   NaryExpr -> VariableAccess -> NaryExpr -> Integer
     * These are used to cache partial results. Note that some unnecessary
     * plucking is done because of this caching. I could clear the caches
     * between two invocations of dagToTree if I really want to keep the
     * size to a minimum.
     */
    
    // variables used for transforming the VC dag into a VC (almost-)tree
    private HashMap dagToVarCache; // (NaryExpr->VariableAccess)
    private HashMap varToTreeCache; // (VariableAccess->NaryExpr)
    private HashMap treeToSizeCache; // (NaryExpr->Integer)
    private HashMap parentsCnt; // counts parents for VC nodes (NaryExpr->Integer)
    private HashSet seenExprs; // used to limit various DAG traversals
    private HashSet usedVariables; // used to collect the variables used by a tree
    private static final String NAME = "ratmpvar"; // used to name variables
    private int varNameCnt; // to make the variable names unique
    
    /* When this is 1 all sharing that makes VCs bigger is eliminated.
     * Bigger values leave some sharing in therefore resulting in slightly
     * bigger VCs. However, they _might_ be processed quicker.
     * TODO: perhaps remove this parameter
     */
    private static final int THRESHOLD = 0;
    
    
    // These are used to represent the compressed graph of the labels.
    private HashMap/*<Node,Integer>*/ nodeToLabelCache;
    private NodeAndLabel[] labels; // identified later on by indices in this array
    private Expr[] postconditions; // maps labels to their postconditions
    private int[] labelState; // unknown, sat, or unsat
    private int[][] labelChildren;
    private int[][] labelParents;
    private int[] dominator; // the immediate dominators
    private int[][] dominated; // the nodes immediately dominated
    private int[] dominatedCnt; // used during the construction of the dominator tree
    
    // used by various DFS-like algorithms
    private boolean[] labelTag; // is thelabel processed
    private int[] labelsDfs; // dfs order of the labels
    private int[] invLabelsDfs; // inverse of labelsDfs
    private int labelOrder; // used during construction

    // Auxiliar information used during the construction of the above
    // NOTE: in a sane programming language I would just use these but
    //       I just hate casting and (un)boxing stuff all over the place.
    private ArrayList/*<NodeAndLabel>*/ labelsTmp;
    private ArrayList/*<HashSet<Integer>>*/ labelParentsTmp;
    private ArrayList/*<HashSet<Integer>>*/ labelChildrenTmp;
    
    
    // NOTE that automatic provers are incomplete and sometimes they will
    // say invalid (interpreted here as SAT) even if the formula is actually
    // unsatisfiable.  We'll make sure we never set the state UNSAT for
    // situations where we don't really know. This way we wan't warn when there
    // really isn't a problem.
    private static final int UNKNOWN = 0; // the prover was not asked or it didn't know
    private static final int SAT = 1;  // satisfiable, the program can reach the label
    private static final int UNSAT = 2; // unsatifiable, we should warn
    
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
    
    /**
     * Returns -1 if |n| is not an interesting node. Otherwise it
     * returns its index. Uses |nodeToLabelCache| to cache the results. 
     */
    private int nodeToLabelIdx(Node n) {
        Integer idx = (Integer)nodeToLabelCache.get(n);
        if (idx != null) return idx.intValue();
        
        int result = -1;
        String label = getLabel(n);
        if (label != null) {
            NodeAndLabel nl = new NodeAndLabel(n, label);
            if (nl.loc != Location.NULL) {
                result = labelsTmp.size();
                labelsTmp.add(nl);
            }
        }
        nodeToLabelCache.put(n, new Integer(result));
        labelParentsTmp.add(new HashSet());
        labelChildrenTmp.add(new HashSet());
        return result;
    }

    private void recComputeDfsOrder(int l) {
        if (labelTag[l]) return;
        labelTag[l] = true;
        labelsDfs[labelOrder] = l;
        invLabelsDfs[l] = labelOrder++;
        for (int i = 0; i < labelChildren[l].length; ++i)
            recComputeDfsOrder(labelChildren[l][i]);
    }
    
    private void computeDfsOrder() {
        labelsDfs = new int[labels.length];
        invLabelsDfs = new int[labels.length];
        labelTag = new boolean[labels.length];
        labelOrder = 0;
        recComputeDfsOrder(0);
    }
    
    // Adds all nodes reachable from [n] (children) to [graphNodes].
    // Also collects the interesting nodes.
    private void recCollectNodes(Node n, int labeledParent) {
        int thisLabel = nodeToLabelIdx(n);
        if (thisLabel != -1) {
            if (graphNodes.contains(n)) return;
            labeledParent = thisLabel;
        }
        graphNodes.add(n);
        HashSet/*<Integer>*/ children = (HashSet)labelChildrenTmp.get(labeledParent);
        
        Enumeration c = n.getChildren().elements();
        while (c.hasMoreElements()) {
            Node child = c.nextElement();
            int childLabel = nodeToLabelIdx(child);
            if (childLabel != -1) {
                HashSet/*<Integer>*/ parents = (HashSet)labelParentsTmp.get(childLabel);
                parents.add(new Integer(labeledParent));
                children.add(new Integer(childLabel));
            }
            recCollectNodes(child, labeledParent);
        }
    }
    
    private int[] toIntArray(HashSet/*<Integer>*/ al) {
        int[] result = new int[al.size()];
        Iterator it = al.iterator();
        int i = 0;
        while (it.hasNext())
            result[i++] = ((Integer)it.next()).intValue(); 
        return result;
    }
    
    /**
     * Collects all nodes reachable from the initial node of |graph| into
     * |graphNodes|. It also constructs a smaller graphs that contains only
     * the labeled (i.e., interesting) nodes.
     */
    private void collectNodes() {
        graphNodes = new HashSet();
        nodeToLabelCache = new HashMap/*<Node,Integer>*/();
        labelsTmp = new ArrayList();
        labelParentsTmp = new ArrayList();
        labelChildrenTmp = new ArrayList();
        Node init = graph.getInitNode();
        String label = getLabel(init);
        NodeAndLabel nl = label == null ? 
            new NodeAndLabel(init) : new NodeAndLabel(init, label);
        labelsTmp.add(nl);
        nodeToLabelCache.put(init, new Integer(0));
        labelParentsTmp.add(new HashSet());
        labelChildrenTmp.add(new HashSet());
        recCollectNodes(init, 0);
        
        // Conver ArrayLists to simple arrays. (I wouldn't do this in a later
        // version of Java.)
        labels = (NodeAndLabel[])labelsTmp.toArray(new NodeAndLabel[0]);
        postconditions = new Expr[labels.length];
        labelParents = new int[labels.length][];
        labelChildren = new int[labels.length][];
        for (int i = 0; i < labels.length; ++i) {
            labelParents[i] = toIntArray((HashSet)labelParentsTmp.get(i));
            labelChildren[i] = toIntArray((HashSet)labelChildrenTmp.get(i));
        }
        
        // These are not needed anymore, don't waste memory
        labelsTmp = null;
        labelParentsTmp = null;
        labelChildrenTmp = null;
        
        // Prepare for later
        labelState = new int[labels.length];
        computeDfsOrder();
        computeDominators();
        printLabelsAndDominators();
    }
    
    private void propagateUnsat(int x) {
        if (labelState[x] != UNKNOWN) return;
        System.err.println("unsat " + x);
        labelState[x] = UNSAT;
        for (int i = 0; i < dominated[x].length; ++i)
            propagateUnsat(dominated[x][i]);
    }
    
    private void propagateSat(int x) {
        if (labelState[x] != UNKNOWN) return;
        System.err.println("sat " + x);
        labelState[x] = SAT;
        propagateSat(dominator[x]);
    }
    
    private void computeDominators() {
        dominator = new int[labels.length];
        for (int i = 0; i < labels.length; ++i) {
            if (labelParents[i].length == 0) 
                dominator[i] = 0;
            else 
                dominator[i] = labelParents[i][0];
        }
        for (int i = 0; i < labels.length; ++i) {
            for (int j = 0; j < labelParents[i].length; ++j) {
                int d = labelParents[i][j];
                while (dominator[i] != d) {
                    if (invLabelsDfs[dominator[i]] < invLabelsDfs[d])
                        d = dominator[d];
                    else
                        dominator[i] = dominator[dominator[i]];
                }
            }
        }
        dominated = new int[labels.length][];
        dominatedCnt = new int[labels.length];
        for (int i = 0; i < labels.length; ++i)
            ++dominatedCnt[dominator[i]];
        for (int i = 0; i < labels.length; ++i) {
            dominated[i] = new int[dominatedCnt[i]];
            dominatedCnt[i] = 0;
        }
        for (int i = 0; i < labels.length; ++i)
            dominated[dominator[i]][dominatedCnt[dominator[i]]++] = i;
    }
    
    private void printLabelsAndDominators() {
        System.out.println("digraph x {");
        for (int i = 0; i < labels.length; ++i) {
            for (int j = 0; j < labelChildren[i].length; ++j)
                System.out.println("" + i + "->" + labelChildren[i][j]);
            System.out.println("" + i + "->" + dominator[i] + "[color=blue]");
        }
        System.out.println("}");
    }

    private String getLabel(Node n) {
        if (n instanceof CodeNode) {
            CodeNode cn = (CodeNode) n;
            String label = assertLabel(cn.getCode());
            return label;
        }
        return null;
    }
    
    private int getParentsCnt(NaryExpr e) {
        Integer i = (Integer)parentsCnt.get(e);
        if (i == null) return 0;
        return i.intValue();
    }
    
    private void incParentsCnt(NaryExpr e) {
        parentsCnt.put(e, new Integer(getParentsCnt(e) + 1));
    }
    
    private void countParents(NaryExpr e) {
        if (seenExprs.contains(e)) return;
        seenExprs.add(e);
        for (int i = 0; i < e.exprs.size(); ++i) {
            Expr o = e.exprs.elementAt(i);
            if (o == null || !(o instanceof NaryExpr)) continue;
            NaryExpr c = (NaryExpr)o;
            incParentsCnt(c);
            countParents(c);
        }
    }
    
    /**
     * Gets (an approximation of) the print size of a tree.
     */
    private int getSize(NaryExpr tree) {
        Integer s = (Integer)treeToSizeCache.get(tree);
        if (s != null) return s.intValue();
        int sz = 1;
        for (int i = 0; i < tree.exprs.size(); ++i) {
            Expr e = tree.exprs.elementAt(i);
            if (e instanceof NaryExpr) 
                sz += getSize((NaryExpr)e);
            else 
                ++sz;
        }
        treeToSizeCache.put(tree, new Integer(sz));
        return sz;
    }
    
    /**
     * Transforms a DAG into an (almost-)tree by eliminating sharing of
     * big structures, where `big' means that the printed version would be
     * bigger with sharing than without.
     * 
     * This function is memoized using the maps dagToVarCache and
     * varToTreeCache.
     * 
     * This function adds the variables used in plucking to the 
     * pluckedVars set.
     * 
     * It assumes that dagParentsCnt maps |e| and all NaryExpr-essions
     * reachable from |e| to the number of parents they have.
     * 
     * TODO: review and maybe rewrite
     */
    private NaryExpr recDagToTree(NaryExpr dag) {
        VariableAccess v = (VariableAccess)dagToVarCache.get(dag);
        if (v != null) return (NaryExpr)varToTreeCache.get(v);
        
        ExprVec ncv = ExprVec.make(); // new children vector
        for (int i = 0; i < dag.exprs.size(); ++i) {
            Expr e = dag.exprs.elementAt(i);
            if (!(e instanceof NaryExpr)) {
                ncv.addElement(e);
                continue;
            }
            NaryExpr c = (NaryExpr)e; // child
            NaryExpr nc = recDagToTree(c); // new (plucked) child
            int ncsz = getSize(nc); // print size of nc
            int ncp = getParentsCnt(c); // parents count
            if (ncsz * (ncp - 1) <= ncp + THRESHOLD) {
                ncv.addElement(nc);
                continue;
            }
            v = (VariableAccess)dagToVarCache.get(c);
            ncv.addElement(v);
        }
        
        // put the result in cache so we don't work twice
        NaryExpr tree = NaryExpr.make(dag.sloc, dag.eloc, dag.op, dag.methodName, ncv);
        v = GC.makeVar(NAME + varNameCnt++);
        dagToVarCache.put(dag, v);
        varToTreeCache.put(v, tree);
        
        return tree;
    }
    
    private void recGetUsedVars(NaryExpr e) {
        if (seenExprs.contains(e)) return;
        seenExprs.add(e);
        for (int i = 0; i < e.exprs.size(); ++i) {
            Expr c = e.exprs.elementAt(i);
            if (c instanceof NaryExpr) recGetUsedVars((NaryExpr)c);
            else if (c instanceof VariableAccess) {
                NaryExpr tree = (NaryExpr)varToTreeCache.get(c);
                if (tree != null) {
                    usedVariables.add(c);
                    recGetUsedVars(tree);
                }
            }
        }
    }
    
    private void getUsedVars(NaryExpr e) {
        //TimeUtil.start("get_used_vars_time");
        seenExprs = new HashSet();
        usedVariables = new HashSet();
        recGetUsedVars(e);
        //TimeUtil.stoprep("get_used_vars_time");
    }
    
    private NaryExpr dagToTree(NaryExpr dag) {
        TimeUtil.start("dag_to_tree_time");
        // count the parents for each node reachable from dag
        parentsCnt = new HashMap();
        seenExprs = new HashSet(); countParents(dag);
        
        // do the plucking
        NaryExpr ne = recDagToTree(dag);
        
        // get the used variables and add their definitions
        getUsedVars(ne);
        ExprVec exprs = ExprVec.make();
        Iterator it = usedVariables.iterator();
        while (it.hasNext()) {
            VariableAccess v = (VariableAccess)it.next();
            Expr def = (Expr)varToTreeCache.get(v);
            exprs.addElement(GC.equiv(v, def));
        }
        exprs.addElement(ne);
        TimeUtil.stoprep("dag_to_tree_time");
        return (NaryExpr)GC.and(exprs);
    }

    // Compute the strongest postcondition (SP) of [n].
    private Expr spDfs(Node n) {
        Expr sp = (Expr) spOfNode.get(n);
        if (sp != null) return sp;

        // compute precondition for [n] as a disjunction of its preconditions
        Enumeration p = n.getParents().elements();
        Expr pre = null;
        while (p.hasMoreElements()) {
            Expr onePre = spDfs(p.nextElement());
            if (pre == null) pre = onePre;
            else pre = GC.or(pre, onePre);
        }

        // compute the sp
        Expr post = n.computeSp(pre);
        
        // cache and store if interesting
        spOfNode.put(n, post);
        int idx = nodeToLabelIdx(n);
        if (idx != -1) postconditions[idx] = post;
        return post;
    }

    private void internalAnalyze(GuardedCmd gc) {
        // initialize the caches used by the DAG-to-(almost-)tree translation
        dagToVarCache = new HashMap();
        varToTreeCache = new HashMap();
        treeToSizeCache = new HashMap();
        
        // construct the graph, assumming that gc doesn't contain VARIN
        GCtoCFDBuilder builder = new GCtoCFDBuilder();
        graph = builder.constructGraph(gc, null);
        if (graph.isEmpty()) return; // nothing to check

        // DBG
        //System.out.println("Constructed graph: " + graph);
        graph.printStats();
         
        // do DFS
        collectNodes();
        spOfNode = new HashMap();
        Node init = graph.getInitNode();
        postconditions[0] = init.computeSp(GC.truelit);
        spOfNode.put(init, postconditions[0]);
        Iterator nodes = graphNodes.iterator();
        while (nodes.hasNext()) spDfs((Node)nodes.next());
        
        // check the interesting nodes and report the possible errors
        // we transform the dag to tree before calling the prover
        for (int i = labels.length - 1; i >= 0; --i) if (labelState[i] == UNKNOWN) {
            if (postconditions[i] instanceof NaryExpr)
                postconditions[i] = dagToTree((NaryExpr)postconditions[i]);
            if (Simplifier.isFalse(postconditions[i]))
                propagateUnsat(i);
            else
                propagateSat(i);
        }
        
        for (int i = 0; i < labels.length; ++i) if (labelState[i] == UNSAT)
            reportUnreachable(labels[i]);
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
    private void reportUnreachable(NodeAndLabel nl) {
        String suffix = " (" + nl.ld.getMsgShort() + ")";
        Assert.notFalse(nl.loc != Location.NULL);
        
        switch (nl.ld.getMsgTag()) {
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
            ErrorSet.warning(nl.loc, ASSERT_WARN + suffix);
            break;
        default:
            // we assume it's code (for now)
            ErrorSet.warning(nl.loc, CODE_WARN + suffix);
        }
    }

    // pre: gc does not contain VARIN commands
    public static void analyze(GuardedCmd gc) {
        new ReachabilityAnalysis().internalAnalyze(gc);
    }
}
