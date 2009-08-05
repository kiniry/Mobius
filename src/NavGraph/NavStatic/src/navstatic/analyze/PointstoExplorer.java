package navstatic.analyze;


import soot.PointsToSet;
import soot.SootClass;
import soot.jimple.NewExpr;
import soot.jimple.spark.pag.AllocNode;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.jimple.spark.sets.PointsToSetInternal;

public class PointstoExplorer extends P2SetVisitor {
	final AbsValue.AbsDisjunct result;
	final Context context;
	private boolean ovniFound = false;
	
    private PointstoExplorer(Context c) { context = c; result = new AbsValue.AbsDisjunct();}

    public void visit (Node node) {
    	if(node instanceof AllocNode) {
    		int id = node.getNumber();
    		if (! context.abstractObjects.containsKey(id)) {
    			Object rawexpr = ((AllocNode) node).getNewExpr();
    			if (rawexpr instanceof NewExpr) {
    				NewExpr newexpr = (NewExpr) rawexpr;
    				SootClass clazz = newexpr.getBaseType().getSootClass();
    				context.abstractObjects.put(id,clazz);
    			} else {
    				result.add(new AbsValue.AbsString(rawexpr.toString()));
    				return;
    			}
    		}
    		result.add(new AbsValue.AbsObject(id));
    	} else {
    		System.err.println("OVNI : " + node.getClass());
    		ovniFound = true;
    	}
    }	

    private AbsValue get() {
    	if(ovniFound) return null;
    	return result;
    }
    
    static AbsValue contents (Context c, PointsToSet ptsarg) {
    	PointsToSetInternal pts = (PointsToSetInternal) ptsarg;
    	PointstoExplorer explorer = new PointstoExplorer(c);
    	pts.forall(explorer);
    	return explorer.get();
    }
}
