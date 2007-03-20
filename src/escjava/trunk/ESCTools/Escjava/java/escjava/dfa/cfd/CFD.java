package escjava.dfa.cfd;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import java.util.List;

import javafe.util.Assert;


import escjava.dfa.cfd.NodeList.Enumeration;

public class CFD  {

    //@ invariant (initNode == null) <==> isEmpty();
    /** The init node of this graph. */
    protected Node initNode;

    /** The exit node of this graph. */
    protected Node exitNode;

    /** The set of exception nodes of this graph. */
    protected/*@ non_null @*/NodeList exceptionNodes;

    /**
     * Initializes a new instance of CFD class. Both init and exit node are set
     * to null. The list of exceptions nodes is initialized with the empty list.
     */
    //@ ensures isEmpty();
    public CFD() {
        this.initNode = null;
        this.exitNode = null;
        this.exceptionNodes = new NodeList();
    }

    /**
     * Creates a copy of this graph. Shallow copies of nodes are created, using Node.shallowCopy(), and then connected as in the original graph.
     */    
    public CFD copy() {
        Clonear clonear = new Clonear();
        return clonear.cloneGraph();
    }

    /**
     * Sets the init node of this graph.
     * 
     * @param in
     *            the new init node for this graph
     */
    public void setInitNode(Node in) {
        this.initNode = in;
    }

    /**
     * Determines whether this graph is an empty graph.
     * 
     * @return true iff this graph is empty
     */
    //@ ensures \result <==> (initNode == null);
    /*@ pure @*/ public boolean isEmpty() {
        return initNode == null;
    }

    /**
     * Sets the exit node of this graph.
     * 
     * @param en
     *            the new exit node for this graph
     */
    public void setExitNode(Node en) {
        this.exitNode = en;
    }

    /*@ normal_behavior
      @   ensures (\result == null) <==> isEmpty(); */
    /*@ pure @*/ public Node getInitNode() {
        return this.initNode;
    }

    /*@ pure @*/ public Node getExitNode() {
        return this.exitNode;
    }

    public /*@ non_null @*/NodeList getExceptionNodes() {
        return this.exceptionNodes;
    }
    
    public void addExceptionNode(/*@ non_null @*/ Node en) {
        this.exceptionNodes.addNode(en);
    }

    public void setExceptionNodes(/*@ non_null @*/NodeList val) {
        this.exceptionNodes = val;
    }

    /**
     * Append the given graph to this one. I.e., if this graph has an exit node,
     * it will be pointing to the init node of cfd. The exception nodes will be
     * unioned.
     */
    //@ requires !cfd.isEmpty();
    public void sequence(/*@ non_null @*/CFD cfd) {
        if (this.exitNode != null) {
            this.exceptionNodes.append(cfd.exceptionNodes);
            this.exitNode.connectTo(cfd.initNode);
            this.exitNode = cfd.exitNode;
        }
    }

    /**
     * The given graph will no longer be an independent graph and will be
     * condsidered as a part of this one.
     */
    public void attach(CFD cfd) {
        /**
         * @todo At this point cfd might be reset, so its invariants are not
         *       broken.
         */
    }

    /**
     * A new init node is created for this graph, this node will be pointing to
     * previous init node and the init node of the given graph. A new exit node
     * is created to which the previous exit nodes will point to. Basically, a
     * diamond structure is created from the current graph and the given one.
     * The exception nodes will be unioned.
     * 
     * @param cfd
     *            a cfd that will be ored with this
     */
    //@ requires !cfd.isEmpty() & !this.isEmpty();
    public void orWith(/*@ non_null @*/CFD cfd) {
        this.orInits(this.initNode, cfd.initNode);
        this.andExits(this.exitNode, cfd.exitNode);
        this.exceptionNodes.append(cfd.exceptionNodes);
    }

    /**
     * If at least one node of the two given one is non-null, creates a new exit
     * node and the given nodes point to it, otherwise the exit node is set to
     * null.
     * 
     * @param e1
     *            a node that will be connected to the new exit node, may be
     *            null
     * @param e2
     *            a node that will be connected to the new exit node, may be
     *            null
     */
    public void andExits(Node e1, Node e2) {
        if (e1 == null && e2 == null) {
            this.exitNode = null;
        } else {
            Node newExit = new CouplingNode();
            if (e1 != null)
                e1.connectTo(newExit);

            if (e2 != null)
                e2.connectTo(newExit);

            this.exitNode = newExit;
        }
    }

    /**
     * Creates a new init node it to the given ones.
     */
    public void orInits(/*@ non_null @*/Node i1, /*@ non_null @*/ Node i2) {
        Node newInit = new CouplingNode();
        newInit.connectTo(i1);
        newInit.connectTo(i2);
        this.initNode = newInit;
    }

    /**
     * Initializes this CFD with a single node, that being both the initial and
     * the exit node of that graph, no exception nodes are created.
     */
    //@ requires n != null;
    //@ ensures !isEmpty();
    public void createSimpleCFD(Node n) {
        this.initNode = n;
        this.exitNode = n;
    }
    
    public static CFD simpleCFD(Node n) {
        CFD retv = new CFD();
        retv.createSimpleCFD(n);
        return retv;
    }
    
    public String toString() {
        LinkedList graphNodes = new LinkedList();

        if (!isEmpty()) {
            collectNodes(this.getInitNode(), graphNodes);
        }

        String retv = "[\n";
        for (Iterator it = graphNodes.iterator(); it.hasNext(); ) {
           retv += (Node)it.next() + "\n";
        }
        retv += "]";
        return retv;
    }
    
    
    // Returns a set of nodes reachable from the initial node. Computed by traversing the graph.
    /*@ ensures \result != null;
      @ ensures isEmpty() <==> \result.isEmpty();
    */
    public List computeNodes() {
        boolean dummy = isEmpty();

        List graphNodes = new ArrayList();
        //@ assert \type(Node) <: graphNodes.elementType;

        if (!dummy)
            collectNodes(initNode, graphNodes);
        
        return graphNodes;
    }
    
    // Adds all nodes reachable from [n] (children) to [graphNodes].
    /*@ public normal_behavior
      @   assignable graphNodes.objectState; 
      @   requires n != null;
      @   requires graphNodes != null;
      @   requires \type(Node) <: graphNodes.elementType;
      @   ensures graphNodes.contains(n);
      */
    private void collectNodes(Node n, List graphNodes) {
        if (graphNodes.contains(n))
            return;
        graphNodes.add(n);
        Enumeration c = n.getChildren().elements();
        while (c.hasMoreElements()) {
            collectNodes(c.nextElement(), graphNodes);
        }
    }
    
    
    
    /**
     * Auxilliary class to construct a copy of this graph.
     * 
     * @author mikolas
     * 
     */
    class Clonear {
        Map cloneMap;

        public Clonear() {
            cloneMap = new HashMap();
        }

        CFD cloneGraph() {
            CFD cloneGraph = new CFD();
            
            // create the clone of the init node, which will clone everything reachable from initNode as well
            cloneGraph.initNode = nodeClone(initNode);
            
            // clone exitNode
            cloneGraph.exitNode = nodeClone(exitNode);
            
            // clone te list of exceptionNodes
            nodeListClone(cloneGraph.exceptionNodes, exceptionNodes);

            return cloneGraph;

        }

        // Populates [dest] with clones of the nodes in [source].
        void nodeListClone(NodeList dest, NodeList source) {
            for (Enumeration e = source.elements(); e.hasMoreElements();) {
                Node node = e.nextElement();
                dest.addNode(nodeClone(node));
            }
        }

        // Clones [orig], if not already cloned, and connects it to the appropriat clones.
        Node nodeClone(Node orig) {
            if (orig == null)
                return null;
            
            if (cloneMap.containsKey(orig)) {
                return (Node) cloneMap.get(orig);
            }

            Node nodeClone = orig.shallowCopy();
            
            cloneMap.put(orig, nodeClone);
            
            nodeListClone(nodeClone.parents, orig.parents);
            nodeListClone(nodeClone.children, orig.children);

            return nodeClone;
        }

    }   
   
    // ------------ debugging code
    
    // ---- printing
    
    // @ requires out != null & a != null & b != null;
    private void printDotEdge(Writer out, Node a, Node b) throws IOException {
        out.write("" + a.hashCode() + " -> " + b.hashCode() + ";\n");
    }
    
    //@ requires out != null;
    private void printDotHeader(Writer out) throws IOException {
        out.write("digraph cfd {\n");
        out.write("node [shape=box]\n");
    }

    //@ requires out != null;
    private void printDotClose(Writer out)  throws IOException{
        out.write("}\n");
    }

    //@ requires out != null;
    public void printToDot(Writer out) throws IOException {
        visited = new HashSet();
        
        // header of the dot file (opening and default values)
        printDotHeader(out);
        
        // traverse and print the graph
        if (!isEmpty())
            printToDot(out, initNode, visited);
        
        // close the dot
        printDotClose(out);            
    }
        

    //@ requires out != null & n != null & visited != null;
    //@ requires \type(Node) <: visited.elementType;
    //@ ensures visited.contains(n);
    private void printToDot(Writer out, Node n, Set visited) throws IOException {
        // avoid multiple visits
        if (visited.contains(n))
            return;
        visited.add(n);

        // print node
        n.printToDot(out);

        // print edges to children and recursively the children
        for (Enumeration en = n.getChildren().elements(); en.hasMoreElements();) {
            Node child = (Node) en.nextElement();
            printDotEdge(out, n, child);
            printToDot(out, child, visited);
        }
    }
    
    
    /* ==== statistics ==== */
    
    
    Set visited;
    
    int chainsCnt = 0, totalLenChains = 0;
    int HASH_MOD = 1007;
    
    //@ requires visited != null;  
    void count(Node g) {
        if (visited.contains(g))
            return;
        
        visited.add(g);
        for (Enumeration en = g.children.elements(); en.hasMoreElements(); ) {
            Node child = en.nextElement();
            
            totalLenChains++;
            
            while (child.getChildren().count == 1 && child.getParents().getCount() == 1) {
                visited.add(child);
                totalLenChains++;
                Node newChild = child.getChildren().getAt(0);
                child = newChild;    
            }
            
            chainsCnt++;
            count(child);
            
        }
    }
    
    
    public void printStats() {
        visited = new HashSet();
        count(this.getInitNode());      
//        System.err.println("Chain count: " + chainsCnt);
//        System.err.println("Edge  count: " + totalLenChains);
//        System.err.println("Avg. length: " + 1.0*totalLenChains / 1.0*chainsCnt);
//        System.err.println("Node count: " + visited.size());
        
        double avgChain = 1.0*totalLenChains / chainsCnt;
        System.err.println(""+ chainsCnt + '\t' + totalLenChains + '\t' + avgChain + '\t' +  visited.size() );
        
        
        OutputStreamWriter ow = new OutputStreamWriter(System.err);
        try {
            ow.write("\n\n===== dot representation of the graph ====\n"); 
            printToDot(ow);
            ow.flush();
        } catch (IOException e) {
            System.err.println("Can't print to the err output.");
        }
        
    }
   

}
