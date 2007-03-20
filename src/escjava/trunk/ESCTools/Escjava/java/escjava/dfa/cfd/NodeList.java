package escjava.dfa.cfd;

/**
 * This class represent a list of nodes.
 */
public class NodeList {
    protected/*@ non_null @*/Node[] nodes;

    protected int count;

    //@ invariant count >= 0;
    //@ invariant nodes.length >= count;
    //@ invariant (\forall int i; i >= 0 & i < count; nodes[i] != null);
    //@ invariant \typeof(nodes) == \type(Node[]);

    /**
     * Initializes a new instance of NodeList class. The node list is
     * initialized with an empty list.
     */
    public NodeList() {
        this.nodes = new Node[1];
        this.count = 0;
    }
    
    
    /**
     * Add a node to this list
     * 
     * @param node
     *            the node to be added
     */
    //@ ensures count == \old(count) + 1;
    public void addNode(/*@ non_null @*/Node node) {
        resize(count + 1);
        nodes[count] = node;
        ++count;
    }

    //@ ensures \result == count;
    /*@ pure @*/ public int getCount() {
        return count;
    }

    //@ ensures \result <==> count == 0;
    /*@ pure @*/ public boolean isEmpty() {
        return count <= 0;
    }

    /**
     * Returns the enumeration that enumerates the nodes
     */
    //@ assignable \nothing;
    public /*@ non_null @*/Enumeration elements() {
        return new Enumeration();
    }

    /**
     * Appends the given list to this one.
     */
    public void append(/*@ non_null @*/NodeList ns) {
        resize(count + ns.count);
        for (int i = 0; i < ns.count; i++)
            nodes[i + count] = ns.nodes[i];
        this.count = count + ns.count;
    }

    /**
     * Clears this list.
     */
    //@ ensures count == 0;
    public void clear() {
        this.count = 0;
    }

    /**
     * Returns true iff this list is empty
     */
    //@ ensures \result <==> this.count <= 0;
    public/*@ pure @*/boolean empty() {
        return this.count <= 0;
    }

    /**
     * Returns true iff this list contains the given node <code>n</node>.
     */
     //@ ensures \result <==> (\exists int j; j >= 0 & j < count; nodes[j] == n);
    /*@ pure @*/ public boolean member(Node n) {
        //@ loop_invariant i >= 0 & i <= count;
        //@ loop_invariant (\forall int j; j >= 0 & j < i; nodes[j] != n);
        for (int i = 0; i < this.count; i++)
            if (n == this.nodes[i])
                return true;

        return false;
    }

    /**
     * Resizes the <code>nodes</code> fields so it is at least
     * <code>newSize</code> long.
     * 
     * @param newSize
     *            desired minimal size of the <code>nodes</code> field
     */
    //@ assignable nodes;
    //@ ensures nodes.length >= newSize;
    void resize(int newSize) {
        if (this.nodes.length < newSize) {
            int newLength = Math.max(this.nodes.length * 2, newSize);
            Node[] newNodes = new Node[newLength];
            for (int i = 0; i < this.count; i++)
                newNodes[i] = this.nodes[i];
            this.nodes = newNodes;
        }
    }


    //@ requires index >= 0 & index < getCount();    
    /*@ pure @*/ public Node getAt(int index) {
        return nodes[index];
    }
    
    public class Enumeration {
        int currentItem = 0;

        //@ invariant currentItem >= 0;

        /*
         * Tests if this enumeration contains more elements.
         */
        //@ ensures \result <==> currentItem < count;
        public/*@ pure @*/boolean hasMoreElements() {
            return currentItem < count;
        }

        /*
         * Returns the next element of this enumeration, if this enumeration
         * object has at least one more element to provide.
         */
        //@ requires hasMoreElements();
        public/*@ non_null @*/Node nextElement() {
            Node retv = nodes[currentItem];
            currentItem++;
            return retv;
        }
    }

}
