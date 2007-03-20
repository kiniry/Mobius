package escjava.dfa.daganalysis;

import escjava.ast.*;
import escjava.translate.*;
import escjava.ast.TagConstants;

import javafe.ast.*;
import javafe.util.Location;
import javafe.util.Assert;

import escjava.dfa.cfd.*;
import escjava.dfa.daganalysis.AlgebraUtils;

import java.util.Hashtable;

public class DAGBackpropagation {
    Hashtable nodeToInfo;

    /**
     * The control-flow diagram on which the analysis is performed.
     *
     */
    CFD cfd;

    /**
     * The predicate that is back-propagated.
     *
     */
    Expr reachPredicate;

    /**
     * The back-propagation will lead to thid  node.
     *
     */
    Node start;

    /**
     * Back-propagation will start from this node.
     *
     */
    Node reach;

    //@ ensures	this.cfd == cfd;
    //@ ensures this.reachPredicate == reachPredicate;
    //@ ensures this.start == start;
    //@ ensures this.reach == reach;
    public DAGBackpropagation(CFD cfd) {
        this.cfd = cfd;
    }

    /**
     * Computes the back-propagation.
     */
    public void backPropagate(Expr reachPredicate, Node start, Node reach) {
        this.reachPredicate = reachPredicate;
        this.start = start;
        this.reach = reach;

        this.initBackProp();
        this.computeIntersections();
        this.backProp();
    }

    /**
     * After the back-propagation was computed returns the computed information for a given node.
     * @param node the node for whic the information requested
     * @return the reach-expression for <code>node</code>
     */
    public /*@ non_null @*/ Expr getInformation(/*@ non_null @*/ Node node) {
        Info i = this.getInfo(node);
        if (i != null)
            return i.getExpr();
        else
            return GC.falselit; // for non-reachable nodes
    }

    /**
     * Initializes the resources needed for back-propagation.
     */
    //@ ensures this.nodeToInfo != null;
    void initBackProp() {
        if (this.nodeToInfo == null)
            this.nodeToInfo = new Hashtable();
        else
            this.nodeToInfo.clear();

        Info reachInfo = new Info(0, this.reachPredicate);
        this.addInfo(this.reach, reachInfo);
    }


    /**
     * Computes the DP values.
     */
    void computeIntersections() {
        this.addDefaultInfo(this.start);
        this.findPath(this.start, this.reach);
    }

    boolean findPath(Node from, Node to) {
        if (from == to)
            return true; // we have reached the goal

        Info fromInfo = this.getInfo(from);

        boolean retv = false;
        NodeList children = from.getChildren();
        for (NodeList.Enumeration e = children.elements(); e.hasMoreElements();) {
            Node child = e.nextElement();
            Info childInfo = this.getInfo(child);
            if (childInfo == null) {
                this.addDefaultInfo(child);
                childInfo = this.getInfo(child);
            }

            if (childInfo.getDP() > 0 || findPath(child, to)) {
                fromInfo.incDP();
                retv = true;
            }
        }

        return retv;
    }

    /**
     * Back-propagates the information between adjacent nodes.
     *
     * @param from the node from which information is propagated from
     * @param to the to which information is propagated to
     */
    protected void backPropAdjacent(Node from, Node to) {
        Expr info = null;
        Expr fromExpr = this.getInfo(from).getExpr();
        if ((to instanceof CouplingNode) || (to instanceof ExceptionNode)) {
            info = fromExpr;
        }
        else
            if (to instanceof CodeNode) {
                CodeNode cn = (CodeNode) to;
                info = backPropAdjacentCodeNode(fromExpr, cn);

            }
            else {
                //@ unreachable;
                Assert.fail("Fall thru on " + to);
            }

        if (info != null) {
            info = variableClosure(info, to.getScope(), from.getScope());
            this.getInfo(to).andExprWith(info);
        }
    }

    Expr variableClosure(Expr expression, GenericVarDeclVec newScope, GenericVarDeclVec oldScope) {
        GenericVarDeclVec enclVars = AlgebraUtils.difference(oldScope, newScope);

        Expr closedExpression = (Expr) expression.clone();

        for (int i = 0; i < enclVars.size(); i++) {
            GenericVarDecl var = enclVars.elementAt(i);
            if (AlgebraUtils.usesVar(var, expression)) {
                LocalVarDecl boundVar = UniqName.newBoundVariable(var.id.toString() + "_scope");
                Expr boundVarAccess = VariableAccess.make(boundVar.id, var.locId, boundVar); 
                closedExpression = GC.subst(var, boundVarAccess, closedExpression);
                closedExpression = GC.forall(boundVar, closedExpression);
            }
        }

        return closedExpression;
    }


    /**
     * Back-propagates the information between adjacent nodes, where the node
     * <code>to</code> is a <code>CodeNode</code>.
     *
     * @param expression the expression to propagate
     * @param to the to which information is propagated to
     */
    //@ requires expression != null;
    //@ requires to != null;
    Expr backPropAdjacentCodeNode(Expr expression, CodeNode to) {
        GuardedCmd command = to.getCode();

        Expr info;
        if (isNoop(command)) {// the command has no effect, simply copy the information
            info = expression;
        }
        else {// compute the weakest precondition otherwise

            // convert asserts to assumes
            if (command.getTag() == TagConstants.ASSERTCMD) {
                command = assertToAssume((ExprCmd) command);
            }

            if (command instanceof ExprCmd) {
                command = stripOfLabelsCommand((ExprCmd) command);
            }

            info = wp(command, expression);
	    info = AlgebraUtils.consolidateAnds(info);
        }

        return info;
    }


    /**
     * Computes normal behaviour - weakest precondtion for a given command and postcondition.
     */
    public static Expr wp(GuardedCmd command, Expr normalPost) {
        if (command instanceof AssignCmd) {
            AssignCmd assignCmd = (AssignCmd) command;
            return wpAssignCommand(assignCmd, normalPost);
        }
        else {
            Expr normalWP = Ejp.compute(command, normalPost,  GC.falselit);
            return normalWP;
        }
    }

    public static Expr wpAssignCommand(AssignCmd assignCmd, Expr normal) {
        int cmdTag = assignCmd.getTag();

        // Calculate the rhs expression
        Expr nuv;
        switch(cmdTag) {
        case TagConstants.GETSCMD:
        case TagConstants.RESTOREFROMCMD:
            nuv = assignCmd.rhs;
            break;
        case TagConstants.SUBGETSCMD:
            // store(v,i,x)

            SubGetsCmd sgc = (SubGetsCmd)assignCmd;
            nuv = GC.nary(Location.NULL, Location.NULL,
                          TagConstants.STORE, sgc.v, sgc.index, sgc.rhs);
            break;
        case TagConstants.SUBSUBGETSCMD:
            // store(v, i1, store(select(v,i1), i2, x))
            SubSubGetsCmd ssgc = (SubSubGetsCmd)assignCmd;

            Expr innermap = GC.nary(Location.NULL, Location.NULL,
                                    TagConstants.SELECT,
                                    ssgc.v, ssgc.index1);
            Expr newinnermap = GC.nary(Location.NULL, Location.NULL,
                                       TagConstants.STORE,
                                       innermap, ssgc.index2, ssgc.rhs);
            nuv = GC.nary(Location.NULL, Location.NULL,
                          TagConstants.STORE,
                          ssgc.v, ssgc.index1, newinnermap);
            break;
        default:
            Assert.fail("Unreachable");
            nuv = null; // dummy assignment
        }

        GenericVarDecl vv  = assignCmd.v.decl;

        Expr wpNormal = GC.subst(vv, nuv, normal);
        return wpNormal;
    }

    static ExprCmd stripOfLabelsCommand(ExprCmd command) {
        Expr pred = command.pred;
        Expr stripped = AlgebraUtils.stripOffLabels(pred);
        return ExprCmd.make(command.cmd, stripped, command.loc);
    }

    static GuardedCmd assertToAssume(ExprCmd assertCmd) {
        Expr pred = assertCmd.pred;
        return GC.assume(pred);
    }

    /**
     * Decides whether a given command has any effect on the reasoning.
     * @param command
     *      the command for which we want to know whether it has any effect
     * @return
     *     <code>true</code>, if  and only if the command doesn't have any effect on the reasoning
     */
    boolean isNoop(GuardedCmd command) {
        int tag = command.getTag();
        switch (tag) {
        case TagConstants.ASSERTCMD:
        case TagConstants.ASSUMECMD:
            ExprCmd ec = (ExprCmd)command;
            Expr pred = ec.pred;
            return AlgebraUtils.isTrueLit(pred);
        default:
            return false;
        }
    }


    /**
     * Performs the back-propagation.
     */
    void backProp() {
        DPNodeList todoList = new DPNodeList();
        Node bp_node = this.reach;

        do {
            NodeList parents = bp_node.getParents();

            // explore the parents of the bp_node node
            for (NodeList.Enumeration e = parents.elements(); e.hasMoreElements();) {
                Node parent = e.nextElement();
                Info parentInfo = this.getInfo(parent);

                if (parentInfo != null && parentInfo.getDP() > 0) {
                    this.backPropAdjacent(bp_node, parent);
                    parentInfo.decDP();
                    if (!todoList.member(parent))
                        todoList.addNode(parent);
                }
            }

            bp_node = todoList.pickReadyNode();
        } while (bp_node != null);
    }

    void addInfo(/*@ non_null @*/Node n, /*@ non_null @*/Info i) {
        this.nodeToInfo.put(n, i);
    }

    void addDefaultInfo(/*@ non_null @*/Node n) {
        Info i = new Info(0, GC.truelit);
        //        Info i = new Info(0, GC.falselit);
        this.addInfo(n, i);
    }

    Info getInfo(/*@ non_null @*/Node n) {
        return (Info) this.nodeToInfo.get(n);
    }

    class DPNodeList extends NodeList {

        int findReadyNode() {
            for (int i = 0; i < count; i++) {
                Info ni = getInfo(nodes[i]);
                if (ni.getDP() == 0) {
                    return i;
                }
            }

            return -1;
        }

        public Node pickReadyNode() {
            if (this.empty())
                return null;

            int readyNodeIndex = this.findReadyNode();
            Node retv = this.nodes[readyNodeIndex];
            this.nodes[readyNodeIndex] = this.nodes[count - 1];
            count--;

            return retv;
        }
    }

    class Info {
        int dp;

        Expr pred;

        public Info(int dp, Expr pred) {
            this.dp = dp;
            this.pred = pred;
        }

        public void incDP() {
            this.dp++;
        }

        public void decDP() {
            this.dp--;
        }

        public void andExprWith(Expr with) {
            this.pred = AlgebraUtils.and(this.pred, with);
        }
	/*
        public void orExprWith(Expr with) {
            this.pred = GC.or(this.pred, with);
	    }*/


        public int getDP() {
            return this.dp;
        }

        public Expr getExpr() {
            return this.pred;
        }

    }

}
