package navstatic.analyze;

import java.io.PrintStream;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.IfStmt;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.Edge;
import soot.tagkit.BytecodeOffsetTag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.CombinedAnalysis;
import soot.toolkits.scalar.CombinedDUAnalysis;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;

public class PathAnalysis extends ForwardBranchedFlowAnalysis <HashSet <BitSet>> {
	public final Map <Integer, DistinguishedEvent> idToEvent;
	public final Map <Stmt, DistinguishedInvoke> stmtToInvoke;
	public final Map <Stmt, DistinguishedBranch> stmtToBranch;
	
	final Context context;
	public final SootClass supportItf;
	public final CombinedAnalysis defuse;

	private int eventCounter = 2; // Note: 1 = entry point.
	private static int methodCounter = 0;
	
	static interface DistinguishedEvent { 
		public void dump(PrintStream out, PathAnalysis pa);
	}
	
	static class DistinguishedInvoke implements DistinguishedEvent {
		final Set <Integer> trackedEdges;
		final Set <Integer> setterEdges;
		final int id;
		final Stmt stmt;
		
		public DistinguishedInvoke(Stmt stmt, int id, Set <Integer> e, Set <Integer> s) {
			trackedEdges = e; setterEdges = s;
			this.stmt = stmt;
			this.id = id;
		}
		
		/**
		 * Tests if this event contains a method changing the current node. 
		 * @return true if there is such a method
		 */
		public boolean isSetter() {	return setterEdges.size() > 0; }
		
		public void dump(PrintStream out, PathAnalysis pa) {
			BytecodeOffsetTag tag = (BytecodeOffsetTag) stmt.getTag("BytecodeOffsetTag");
			int offset = (tag == null) ? -1 : tag.getBytecodeOffset();
			out.println("  <event id=\"" + id + "\" offset=\"" + offset + "\">");
			for (int ref: setterEdges) { out.println("    <setterref id=\"" + ref + "\"/>");	}
			for (int ref: trackedEdges)  { out.println("    <trackedref id=\"" + ref + "\"/>");	}
			if (isSetter()) pa.dump(out, stmt);
			out.println("  </event>");
		}
	}
	
	public void registerInvoke(Stmt stmt, Set <Integer> e, Set<Integer> s) {
		int id = eventCounter ++;
		DistinguishedInvoke dev = new DistinguishedInvoke(stmt,id,e,s);
		stmtToInvoke.put(stmt, dev);
		idToEvent.put(id, dev);
	}
	
	static class DistinguishedBranch implements DistinguishedEvent {
		final public Stmt stmt;
		final int idPos, idNeg;
		final Test test;
		
		DistinguishedBranch(PathAnalysis pa, IfStmt stmt, int idPos, int idNeg) {
			this.stmt = stmt;
			this.idPos = idPos;
			this.idNeg = idNeg;
			this.test = new Test(pa,stmt);
		}
		
		public void dump(PrintStream out, PathAnalysis pa) {
			BytecodeOffsetTag tag = (BytecodeOffsetTag) stmt.getTag("BytecodeOffsetTag");
			int offset = (tag == null) ? -1 : tag.getBytecodeOffset();
			out.println("  <branch id=\"" + idPos + "\" offset=\"" + offset + "\">");
			out.println("    " + test);
			out.println("  </branch>");
		}
	}
		
	public void registerBranch(PathAnalysis pa, IfStmt stmt) {
		int idPos = eventCounter ++;
		int idNeg = eventCounter ++;
		DistinguishedBranch dev = new DistinguishedBranch(pa, stmt,idPos,idNeg);
		stmtToBranch.put(stmt, dev);
		idToEvent.put(idPos, dev);
		idToEvent.put(idNeg, dev);
	}
	
	PathAnalysis(Context context, SootMethod meth, SootClass supportItf) {
    	super(new ExceptionalUnitGraph(meth.getActiveBody()));
    	this.context = context;
    	this.supportItf = supportItf;
    	defuse = CombinedDUAnalysis.v((UnitGraph) graph);
    	idToEvent = new HashMap <Integer, DistinguishedEvent> ();
    	stmtToInvoke = new HashMap <Stmt, DistinguishedInvoke> ();
    	stmtToBranch = new HashMap <Stmt, DistinguishedBranch> ();
		for(Iterator <Edge> it = context.cg.edgesOutOf(meth); it.hasNext(); ){
			Edge directCall = it.next();
			Stmt invokeStmt = directCall.srcStmt();
			HashSet <Edge> invoked = new HashSet <Edge> ();
			invokedMethods(directCall, invoked);
			
			Set <Integer> trackedEdges = new HashSet <Integer> ();
			Set <Integer> setterEdges = new HashSet <Integer> ();
			Set <SootMethod> trackedMethods = context.rules.trackedMethods;
			Set <SootMethod> setterMethods = context.rules.setterMethods;
			
			for(Edge edge : invoked) {
				SootMethod tgt = edge.tgt();
				if(trackedMethods.contains(tgt)) {
					int ref = mark(edge);
					trackedEdges.add(ref);
				}
				if(setterMethods.contains(tgt)) {
					int ref = mark(edge);
					setterEdges.add(ref);
				}
			}
			
			if (trackedEdges.size() > 0 || setterEdges.size() > 0)  
				registerInvoke(invokeStmt,trackedEdges, setterEdges);
		}
		
    	for(Unit ub: meth.getActiveBody().getUnits()) {
    		Stmt stmt = (Stmt) ub;
    		System.err.print(".");
    		if (stmt instanceof IfStmt) registerBranch(this, (IfStmt) stmt);
    	}
    	doAnalysis();
    }

	private int mark(Edge edge) {
		Stmt stmt = edge.srcStmt();
		MarkTag tag = (MarkTag) stmt.getTag("MarkTag");
		if(tag == null) {
			int id = methodCounter++;
			stmt.addTag(new MarkTag(id));
			return id;
		} else return tag.getMark();
	}
	
	private void invokedMethods(Edge e, Set <Edge> found) {
		
		if (! found.contains(e)) {
			found.add(e);
			SootMethod tgt = e.tgt();
			for(Iterator <Edge> it = context.cg.edgesOutOf(tgt); it.hasNext(); ) 
				invokedMethods(it.next(), found);
		}
	}
	
    protected void copy(HashSet<BitSet> source, HashSet<BitSet> dest) {
    	dest.clear();
    	dest.addAll(source);
    }

    protected HashSet<BitSet> entryInitialFlow() {
    	HashSet <BitSet> flow = new HashSet <BitSet>();
    	BitSet init = new BitSet();
    	init.set(1);
    	flow.add(init);
    	return flow;
    }

    protected HashSet<BitSet> newInitialFlow() {
    	return new HashSet <BitSet> ();
    }

    protected BitSet setBit(BitSet bs, int n) {
    	if (bs.get(n)) return bs;
    	BitSet r = (BitSet) bs.clone();
    	r.set(n);
    	return r;
    }

    protected void flowThrough(HashSet<BitSet> in, Unit unit,
    						   List <HashSet<BitSet>> fallOut, List <HashSet<BitSet>>branchOut) {
    	Stmt stmt = (Stmt) unit;
    	if (stmt instanceof IfStmt) {
    		DistinguishedBranch br = this.stmtToBranch.get(stmt);
    		for(BitSet elt : in) {
    			BitSet posSet = setBit(elt,br.idPos);
    			BitSet negSet = setBit(elt,br.idNeg);
    			for(HashSet <BitSet> fallOutFlow : fallOut)
    				fallOutFlow.add(posSet);
    			for(HashSet <BitSet> branchOutFlow : branchOut)
    				branchOutFlow.add(negSet);
    		}
    	} else if (stmt.containsInvokeExpr()) {
    		DistinguishedInvoke dev = stmtToInvoke.get(stmt);
    		if (dev == null) {
    			for(HashSet <BitSet> outFlow : fallOut) outFlow.addAll(in);
    		} else if (dev.isSetter()) {
    			for(HashSet <BitSet> outFlow : fallOut) {
    				BitSet singleton = new BitSet(dev.id);
    				singleton.set(dev.id);
    				outFlow.add(singleton);
    			}
    		} else {
    			for(BitSet elt : in) {
    				BitSet newElt = setBit(elt,dev.id);
    				for(HashSet <BitSet> fallOutFlow : fallOut)
    					fallOutFlow.add(newElt);
    			}
    		}
    	} else {
    		for(HashSet <BitSet> flow : fallOut) flow.addAll(in);
    		for(HashSet <BitSet> flow : branchOut) flow.addAll(in);
    	}
    }

    protected void merge(HashSet <BitSet> in1, HashSet<BitSet> in2, HashSet <BitSet> out) {
    	out.clear();
    	out.addAll(in1);
    	out.addAll(in2);
    }
    
    public void dump(PrintStream out, Stmt stmt) {
    	for(BitSet path:getFlowBefore(stmt)) {
    		int start = -1;
    		Set <Integer> pos = new HashSet<Integer> ();
    		Set <Integer> neg = new HashSet<Integer> ();
    		Set <Integer> evt = new HashSet<Integer> ();
    		for (int id = path.nextSetBit(0); id >= 0; id = path.nextSetBit(id+1)) {
    			if (id==1) { start = 0; continue; }
    			DistinguishedEvent dev = idToEvent.get(id);
    			if (dev instanceof DistinguishedInvoke ) {
    				if (((DistinguishedInvoke) dev).isSetter())	start = id; 
    				else evt.add(id);
    				continue;
    			}
    			int realId = ((DistinguishedBranch) dev).idPos;
    			if (id == realId) pos.add(realId); else neg.add(realId);
    		}
    		out.println("    <path start=\"" + start + "\">");
    		for (int id: pos) out.println("      <branchref id=\"" + id + "\" pos=\"Y\"/>");
    		for (int id: neg) out.println("      <branchref id=\"" + id + "\" pos=\"N\"/>");
    		for (int id: evt) out.println("      <eventref id=\"" + id + "\"/>");
    		out.println("    </path>");
    	}
    }
    
    public void dump(PrintStream out) {
    	for(DistinguishedEvent dev: stmtToInvoke.values()) dev.dump(out, this);
    	for(DistinguishedEvent dev: stmtToBranch.values()) dev.dump(out, this);
    }
}
