package bytecode_wp.vcg;

import jack.util.Logger;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.javatype.JavaReferenceType;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.bcexpression.ref.Reference;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;
import bytecode_wp.formula.PredicateSymbol;
import bytecode_wp.formula.Quantificator;
import bytecode_wp.formula.QuantifiedFormula;

/**
 * 
 * @author mpavlova
 * 
 * The class models a verification condition for
 * a particular execution path and assertion
 */
public class VCGPath extends Expression {
	private Hashtable hypPool;

	private  Hashtable goalPool;

	private  Vector vcs;
	
	/**
	 * the offset of the instruction to which this verification conditions belong
	 */
	private  int instrIndex;

	
	
	public static final Integer TRUE_AS_HYPOTHESIS = new Integer(-1);


	
	/**
	 * a field that indicates if the trivial lemmas are removed or not
	 */
	private static boolean SIMPLIFY = true;
	public VCGPath() {
		
	}

	public VCGPath(Hashtable _hypPool, Hashtable _goalPool, Vector _vcs) {
		hypPool = _hypPool;
		goalPool = _goalPool;
		vcs = _vcs;
		
	}

	public Expression substitute(Expression e1, Expression e2) {
		substituteHyp(e1, e2);
		substituteGoal(e1, e2);
		simplify();
		return this;
	}

	/**
	 * adds a new goal <code>goal</code> of type <code>type</code> 
	 * The method adds the new goal in the internal vector goals
	 * and creates a new VC for this goal which is added in the 
	 * internal list of vcs. 
	 * 
	 * @param type - the type of the goal @see <code>vcg.VcType</code>
	 * @param goal
	 */
	public VC addGoal(byte type, Formula goal) {
		if (goal == Predicate0Ar.TRUE ) {			
			return null;
		}
		initGoals();
		Integer key = IDGenerator.getInt();
		goalPool.put(key, goal);
		VC vc = new VC(type, key);
		initVCS();
		vcs.add(vc);
		return vc;
	}

	public VC addGoal(byte type, Formula goal, int position) {
		if (goal == Predicate0Ar.TRUE ) {			
			return null;
		}
		initGoals();
		Integer key = IDGenerator.getInt();
		goalPool.put(key, goal);
		VC vc = new VC(type, key, position);
		initVCS();
		vcs.add(vc);
		return vc;
	}
	
	public VC addGoal(byte type, Formula goal, String exc) {
		if (goal == Predicate0Ar.TRUE ) {			
			return null;
		}
		initGoals();
		Integer key = IDGenerator.getInt();
		goalPool.put(key, goal);
		VC vc = new VC(type, key, exc);
		initVCS();
		vcs.add(vc);
		return vc;
	}
	/**
	 * adds an additional  hypothesis only to the modifies goals concerning newly created objects 
	 * For example, the following method is legal:
	 *   
	 *   C {
	 *   int a;
	 *   //modifies nothing;
	 *   m() {
	 *     C c = new C(); // ref_c
	 *     c.a = 2
	 *   }
	 *   }
	 *   The proof obligation concerning the modifies clause will then contain a conjunct of the form:
	 *   
	 *   forall x. x != ref_c ==> a(x) == a+(ref_c -> 2) (x)
	 * @param pos - from what bytecode position originates the hypothesis
	 * @param newRef - the newly created reference for which a new hypothesis is added
	 * @return the identifier of the newly created hypothesis in the pool of hypothesis
	 */
	public void addHypForNewInstanceInModifiesGoals( Reference newRef) {
		if (vcs == null) {
			return;
		}
		for ( int i =0; i < vcs.size(); i++) {
			VC vc = (VC)vcs.elementAt(i);
			if (vc.getType() == VcType.MODIFIES) {
				Formula goalMod= (Formula)goalPool.get( vc.getGoal());
				if ( goalMod instanceof QuantifiedFormula) {
					Quantificator q = ((QuantifiedFormula)goalMod ).getQuantificator(); 
					if ( JavaReferenceType.subType((JavaType)newRef.getType(), (JavaType)q.getBoundVars()[0].getType() ) ) {
						Predicate2Ar objDiffNewRef = new Predicate2Ar( q.getBoundVars()[0], newRef, PredicateSymbol.NOTEQ);
						Formula f = (Formula)goalMod.getSubExpressions()[0];
						if (f.getConnector() == Connector.IMPLIES) {
							Formula hyps = (Formula) f.getSubExpressions()[0];
							hyps = Formula.getFormula(hyps , objDiffNewRef, Connector.AND);
							f.setSubExpressions(new Expression[]{hyps, f.getSubExpressions()[1]} );
							
						}
					}
				}
			}
			
		}
		
	}
	/**
	 * adds a new hypothesis to the pool, if it is not false returns the id of
	 * the hypothesis
	 * 
	 * @param fromInstr -
	 * @param f
	 */
	public Integer addHyp(int pos, Formula h) {
		//if the hypothesis is the predicate true
		// do not add it
		if (h == Predicate0Ar.TRUE ) {
			return TRUE_AS_HYPOTHESIS;
		}
		initHyp();
		// bad as the object is created and may be it won't be used
		Hypothesis hyp = new Hypothesis(pos, h);
		
		// check if the hypothesis is already in the pool of hypothesis.
		// If the hypothesis is already in the hypothesis pool return the 
		// key of the object in the hashtable
		// that is corresponding to the hypothesis
		boolean contains = hypPool.containsValue(h);
		if (contains ) {
			Enumeration en = hypPool.keys();
			while (en.hasMoreElements() ) {
				Integer key = (Integer)en.nextElement();
				Hypothesis _hyp =(Hypothesis)goalPool.get(key);
			
				if (hyp.equals(_hyp)) {
					return key;
				}
			}
		}
		
		Integer id = IDGenerator.getInt();
		hypPool.put(id, hyp);
		return id;
	}

	/**
	 * add a new hypothesis to every goal
	 * 
	 * @param h
	 */
	public void addHypsToVCs(Integer id) {
		if (vcs == null) {
			return;
		}
		for (int i = 0; i < vcs.size(); i++) {
			VC vc = (VC) vcs.elementAt(i);
			vc.addHyp((Integer) id);
		}

	}

	private void initHyp() {
		if (hypPool == null) {
			hypPool = new Hashtable();
		}
	}

	private void initGoals() {
		if (goalPool == null) {
			goalPool = new Hashtable();
		}
	}

	private void initVCS() {
		if (vcs == null) {
			vcs = new Vector();
		}
	}

	private void substituteHyp(Expression e1, Expression e2) {
		if (hypPool == null) {
			return;
		}
		Enumeration keys = hypPool.keys();
		Hypothesis hyp = null;
		while (keys.hasMoreElements()) {
			Integer key = (Integer) keys.nextElement();
			hyp = (Hypothesis) hypPool.get(key);
			hyp.substitute(e1, e2);
			hypPool.put(key, hyp);
		}
	}

	private void substituteGoal(Expression e1, Expression e2) {
		if (goalPool == null) {
			return;
		}
		Enumeration keys = goalPool.keys();
		while (keys.hasMoreElements()) {
			Integer key = (Integer) keys.nextElement();
			Formula goal = (Formula) goalPool.get(key);
			goal = (Formula)goal.substitute(e1, e2); 
		}
	}

	/**
	 * this method makes a copy of this object.
	 * 
	 * @return
	 */
	public Expression copy() {
		Vector vcCp = copyVCS();
		Hashtable goalPoolCp = copyGoalPool(vcCp);
		Hashtable hypPoolCp = copyHypPool(vcCp);
		VCGPath vcgPath = new VCGPath(hypPoolCp, goalPoolCp, vcCp );
		return vcgPath;
	}

	private Vector copyVCS() {
		if (vcs == null) {
			return null;
		}
		Vector vcsCopy = new Vector();
		for (int i = 0; i < vcs.size(); i++) {
			VC vcCopy = ((VC) vcs.elementAt(i)).copy();
			vcsCopy.add(vcCopy);
		}
		return vcsCopy;
	}

	private Hashtable copyGoalPool(Vector vcToSet) {
		if (goalPool == null) {
			return null;
		}
		Hashtable poolCopy = new Hashtable();
		Enumeration keys = goalPool.keys();
		while (keys.hasMoreElements()) {
			Integer key = (Integer) (keys.nextElement());
			Expression expCopy = ((Expression) goalPool.get(key)).copy();
			Integer keyCp = IDGenerator.getInt();
			poolCopy.put(keyCp, expCopy);
			if (vcToSet != null) {
				for (int i = 0; i < vcToSet.size(); i++) {
					VC vc = (VC) vcToSet.elementAt(i);
					vc.changeGoalKeys(key, keyCp);
				}
			}
		}
		return poolCopy;
	}

	/**
	 * copies a pool and changes the keys of the elements in the pool
	 * 
	 * @param hypPool
	 * @param vcToSet
	 * @return
	 */
	private Hashtable copyHypPool(Vector vcToSet) {
		if (hypPool == null) {
			return null;
		}
		Hashtable poolCopy = new Hashtable();
		Enumeration keys = hypPool.keys();
		while (keys.hasMoreElements()) {
			Integer key = (Integer) (keys.nextElement());
			Hypothesis expCopy = ((Hypothesis) hypPool.get(key)).copy();
			Integer keyCp = IDGenerator.getInt();
			poolCopy.put(keyCp, expCopy);
			if (vcToSet != null) {
				for (int i = 0; i < vcToSet.size(); i++) {
					VC vc = (VC) vcToSet.elementAt(i);
					vc.changeHypKeys(key, keyCp);
				}
			}

		}
		return poolCopy;
	}

	public void merge(VCGPath vcg) {

		Hashtable goalPoolToMerge = vcg.getGoalPool();
		initGoals();
		if (goalPoolToMerge != null) {	
			goalPool.putAll(goalPoolToMerge);
		}
		Hashtable hypPoolToMerge = vcg.getHypPool();
		initHyp();
		if ( hypPoolToMerge != null){
			hypPool.putAll(hypPoolToMerge);
		}
		Vector vcsToMerge = vcg.getVcs();
		initVCS();
		if (vcsToMerge == null) {
			return;
		}
		vcs.addAll(vcsToMerge);

	}

	public Hashtable getGoalPool() {
		return goalPool;
	}

	public Hashtable getHypPool() {
		return hypPool;
	}

	public Vector getVcs() {
		return vcs;
	}

	/**
	 * @param vcgs
	 * @return
	 */
	public static VCGPath mergeAll(Vector vcgs) {
		Enumeration en = vcgs.elements();
		VCGPath merge = new VCGPath();
		while (en.hasMoreElements()) {
			VCGPath f = (VCGPath) en.nextElement();
			merge.merge(f);
		}
		return merge;
	}

	/**
	 * geneerates verification condition for thrown unhandled exceptions 
	 * which does not have an explicite postcondition and thus, 
	 * have a postcondition by default equal to false
	 * 
	 * @return a VCGPath object
	 */
	public static VCGPath initVCwithGoalFalse() {
		VCGPath vcFalse = new VCGPath();
		vcFalse.addGoal(VcType.INSTR_THROW_EXC, Predicate0Ar.FALSE);
		return vcFalse;
	}

	public Expression atState(int pos, Expression expr) {
		hypAtState(pos, expr);
		goalAtState(pos, expr);
		return this;
	}

	private void hypAtState(int pos, Expression expr) {
		if (hypPool == null) {
			return;
		}
		Enumeration keys = hypPool.keys();
		while (keys.hasMoreElements()) {
			Integer key = (Integer) keys.nextElement();
			Hypothesis hyp = (Hypothesis) hypPool.get(key);
			hyp.atState(pos, expr);
			//hypPool.put(key, hyp);
		}
	}

	private void goalAtState(int pos, Expression expr) {

		if (goalPool == null ) {
			return;
		}

		Enumeration keys = goalPool.keys();
		while (keys.hasMoreElements()) {
			Integer key = (Integer) keys.nextElement();
			Expression goal = (Formula) goalPool.get(key);
			goal = goal.atState(pos, expr);
			goalPool.put(key, goal);
		}
	}
	
	public Expression loopModifArrayAtState(int instrIndex, Expression expr ) {
		goalLoopModifArrayAtState(instrIndex, expr );
		hypLoopModifArrayAtState(instrIndex, expr );
		return this;
	}
	
	private void hypLoopModifArrayAtState(int instrIndex, Expression expr) {
		if (hypPool == null) {
			return;
		}
		Enumeration keys = hypPool.keys();
		while (keys.hasMoreElements()) {
			Integer key = (Integer) keys.nextElement();
			Hypothesis hyp = (Hypothesis) hypPool.get(key);
			hyp.loopModifArrayAtState(instrIndex, expr);
			//hypPool.put(key, hyp);
		}
	}

	private void goalLoopModifArrayAtState(int instrIndex, Expression expr) {
		if (goalPool == null ) {
			return;
		}
		Enumeration keys = goalPool.keys();
		while (keys.hasMoreElements()) {
			Integer key = (Integer) keys.nextElement();
			Expression goal = (Formula) goalPool.get(key);
			goal = goal.loopModifArrayAtState(instrIndex, expr);
			goalPool.put(key, goal);
		}
	}

	/**
	 * this method removes the lemmas which are trivial
	 *  if the flag simplifyLevel is set to  REMOVE_TRIVIAL.
	 * A trivial lemma either  proves true, i.e. is of the form * ==> true
	 * or has a contradiction in its hypothesis. For finding contradictions
	 * the private  method @see <code>isHypContradiction</code> is used
	 * Removes the object vc of this form
	 * 
	 */
	public Expression simplify() {
		if (! SIMPLIFY) {
			return this;
		} 
		
		if (vcs == null) {
			return this;
		}
		if (hypPool != null) {
			Enumeration hyp = hypPool.elements();
			while (hyp.hasMoreElements()) {
				Hypothesis h = (Hypothesis)hyp.nextElement();
				h.simplify();
			}
		}
		
		if (goalPool != null) {
			Enumeration keys = goalPool.keys();
			while (keys.hasMoreElements()) {
				Integer key = (Integer)keys.nextElement();
				Formula f = (Formula)goalPool.get(key);
				f = (Formula)f.simplify();
				goalPool.put( key, f);
			}
		}
		for (int i = 0; i < vcs.size() ; i++) {
			VC vc = (VC)vcs.elementAt(i);
			if (isTrivial(vc) ) {
				vcs.remove(vc);
				continue;
			}
			if (isHypFalse(vc)) {
				vcs.remove(vc);
				continue;
			} 
			if ( isHypContradiction(vc)) {
				vcs.remove(vc);
				continue;
			}
		}
		return this;
	}
	/**
	 * checks if the goal follows trivially of the hypothesis Here this means to
	 * check that the goal equals some of teh hypothesis
	 * 
	 * @return true if the vc is trivial
	 */
	private boolean isTrivial(VC vc) {
		Integer goalKey = vc.getGoal();
		Formula goal = (Formula) goalPool.get( goalKey);
		if (goal == Predicate0Ar.TRUE) {
			return true;
		}
		Vector hypKeys = vc.getHyps();
		if ( (hypKeys == null ) || (hypKeys.size() == 0)) {
			return false;
		}
		// if the goal coincides with one of the hypothesis then the lemma is trivial
		for ( int h = 0; h < hypKeys.size(); h++) {
			Integer hypKey = ( (Integer)hypKeys.elementAt( h) );
			if (hypKey == null) {
				continue;
			}
			Formula hypoF =  ((Hypothesis) ( hypPool.get(hypKey))).getFormula();
			if (hypoF.equals( goal) ) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * Returns whether a contradiction is found in hypothesis. The
	 * contradictions are of the form
	 * <UL>
	 * <li> a hypothese is <code>true == false</code> or
	 * <code>false == true</code>
	 * <li> a hypothese matches with <code>a == null</code> and another with
	 * <code>!a == null</code>
	 * <li> a hypothese matches with <code>a == true</code> and another with
	 * <code>a == false</code>
	 * </UL>
	 * 
	 * @return <code>true</code> if a contradiction is found,
	 *         <code>false</code> otherwise
	 */
	private boolean isHypContradiction(VC vc) {
		Vector hyps = vc.getHyps();
		if ( hyps == null) {
			return false;
		}
		for (int i = 0; i < hyps.size(); i++) {
			Integer h1 = (Integer) hyps.elementAt(i);
			Formula f1 = (Formula) (((Hypothesis)hypPool.get( h1)).getFormula() );
			for (int j = i + 1; j < hyps.size(); j++) {
				Integer h2 = (Integer) hyps.elementAt(j);
				Formula f2 = (Formula) (((Hypothesis)hypPool.get( h2)).getFormula() );
				if (Formula.isContradiction(f1, f2)) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean isHypFalse(VC vc) {
		Vector hyps = vc.getHyps();
		if ( hyps == null) {
			return false;
		}
		for (int i = 0; i < hyps.size(); i++) {
			Integer h1 = (Integer) hyps.elementAt(i);
			Formula f1 = (Formula) (((Hypothesis)hypPool.get( h1)).getFormula() );
			if (f1 == Predicate0Ar.FALSE ) {
				return true;
			}
		}
		return false;
	}



	public String toString(int ind) {
		String thm = null;
		String hyps = null;
		VC vc = (VC) vcs.elementAt(ind);
		Vector keyHyp = vc.getHyps();
		if (keyHyp == null) {
			hyps = hyps + "]";
		} else {
			for (int j = 0; j < keyHyp.size(); j++) {
				Integer hKey = (Integer) keyHyp.elementAt(j);
				Hypothesis h = (Hypothesis) hypPool.get(hKey);
				if (j == keyHyp.size() ) {
					hyps = hyps  + h.toString();
				} else {
					hyps = hyps  + h.toString() + " ; ";
				}
			}
			hyps = hyps + "]";
		}
		Integer goalKey = vc.getGoal();
		Formula goal = (Formula) goalPool.get(goalKey);
		String goalString = "Goal:  " + ":" + goal;
		thm = hyps + goalString + "\n";
		return thm;
	}
	
	public String toString() {

		String ths = " \n Theorems  ";
		if (vcs == null) {
			return "" + Predicate0Ar.TRUE;
		}
		for (int i = 0; i < vcs.size(); i++) {
			String thm = null;
			VC vc = (VC) vcs.elementAt(i);

			String hyps = "Hypothesis : [ ";
			Vector keyHyp = vc.getHyps();
			if (keyHyp == null) {
				hyps = hyps + "]";
			} else {
				for (int j = 0; j < keyHyp.size(); j++) {
					Integer hKey = (Integer) keyHyp.elementAt(j);
					Hypothesis h = (Hypothesis) hypPool.get(hKey);
					if (j == keyHyp.size() ) {
						hyps = hyps  + h.toString();
					} else {
						hyps = hyps  + h.toString() + " ; ";
					}
				}
				hyps = hyps + "]";
			}
			Integer goalKey = vc.getGoal();
			Formula goal = (Formula) goalPool.get(goalKey);
			String typeGoal = "";
			if ( vc.getType() == VcType.ASSERTION ) {
				typeGoal = "ASSERTION";
			}  else if ( vc.getType() == VcType.HISTORY_CONSTR) {
				typeGoal = "HISTORY_CONSTR";
			} else if ( vc.getType() == VcType.INSTANCE_INVARIANT) {
				typeGoal = "INSTANCE_INVARIANT";
			} else if ( vc.getType() == VcType.STATIC_INVARIANT) {
				typeGoal = "STATIC_INVARIANT";
			} else if ( vc.getType() == VcType.INSTR_THROW_EXC) {
				typeGoal = "INSTR_THROW_EXC";
			} else if ( vc.getType() == VcType.LOOP_TERMINATION) {
				typeGoal = "LOOP_TERMINATION";
			} else if ( vc.getType() == VcType.LOOPINIT) {
				typeGoal = "LOOP_INIT";
			} else if ( vc.getType() == VcType.MODIFIES) {
				typeGoal = "MODIFIES";
			} else if ( vc.getType() == VcType.LOOPPRESERV ) {
				typeGoal = "LOOP_PRESERV";
			} else if ( vc.getType() == VcType.NORM_POST) {
				typeGoal = "NORM_POST";
			} else if ( vc.getType() == VcType.PRE_METH_CALL) {
				typeGoal = "PRE_METH_CALL";
			} 
			
			String goalString = null;
			if (vc.getPosition() == -1) {
				goalString = "Goal:" + typeGoal ;
			} else {
				goalString = "Goal:" + typeGoal  + " atInd : "  + vc.getPosition() ;
			}
			if (vc.getExc() != null )  {
				goalString = goalString + " exc : "	 + vc.getExc();
			}
			goalString = goalString + " : " + goal;
			thm = hyps + goalString + "\n";
			ths = ths + thm;
		}
		return ths;

	}

	public void toStringHyps() {
		Enumeration en = hypPool.elements() ;
		while (en.hasMoreElements()) {
			Hypothesis h = (Hypothesis)en.nextElement();
			Logger.get().println(h.toString());
		}
	}
	
	public void toStringGoals() {
		Enumeration en = goalPool.elements() ;
		while (en.hasMoreElements()) {
			Formula h = (Formula)en.nextElement();
			Logger.get().println(h.toString());
		}
	}
	

	/**
	 * returns the formula corresponding to the vc at index <code>ind</code>
	 * @param ind
	 * @return
	 * @throws ArrayIndexOutOfBoundsException if the index is bigger than the
	 * vector length or smaller than 0
	 */
	public Formula getProveObligationAt(int ind) {
		VC vc = (VC)vcs.elementAt( ind);
		Vector hypKey = vc.getHyps();
		if ( hypKey == null ) {
			Formula goal = (Formula) goalPool.get( vc.getGoal());
			return goal;
		}

		Vector hypF = null;

		for (int j= 0; j < hypKey.size();j++ ) {
			Hypothesis h = (Hypothesis) hypPool.get((Integer) hypKey.elementAt(j));
			Formula f = h.getFormula();
			if (checkIfInHypothesis(hypF, f )) {
				continue;
			}
			if (hypF == null) {
				hypF = new Vector();
			}
			hypF.add( f);
		}
		Formula  hYp = Formula.getFormula(hypF, Connector.AND );
		Formula goal = (Formula) goalPool.get( vc.getGoal());
		Formula pog = Formula.getFormula(hYp, goal, Connector.IMPLIES );
		return pog;
		
	}
	
	/**
	 * 
	 * @return the formulas that are the hypothesis for 
	 * the proof obligation at index @param ind
	 * 
	 */
	public Vector getHypothesisAt( int ind) {
		VC vc = (VC)vcs.elementAt( ind);
		Vector hypKey = vc.getHyps();
		
		Vector hypF = new Vector();
		if (hypKey == null) {
			Hypothesis h = new Hypothesis(0, Predicate0Ar.TRUE );
			hypF.add( h);
			/*hypF.add(Predicate0Ar.TRUE);*/
			return hypF;
		}
		
		for (int j= 0; j < hypKey.size();j++ ) {
			Hypothesis h = (Hypothesis) hypPool.get((Integer) hypKey.elementAt(j));
	/*		//to be removed////
			Formula f = h.getFormula();
			if (checkIfInHypothesis(hypF, f )) {
				continue;
			}
			hypF.add( f);
			//to be removed////////////////
*/			
			//new code add also checkIfInHypothesis(hypF, f );
			//if(h.getFormula().equals(Predicate0Ar.TRUE))
			//	continue;
			hypF.add( h);
		}
		return  hypF;
	}
	
	/**
	 * @return a vector of the conjuncts that constitute the goal
	 * of the verification condition with index ind
	 * 
	 */
	public Vector getGoalsAt( int ind) {
		VC vc = (VC)vcs.elementAt( ind);
		Formula goal = (Formula) goalPool.get( vc.getGoal());
		Vector goalsInConj  = goal.elimConj();
		return goalsInConj;
	}
	

	/**
	 * @return a vector of the conjuncts that constitute the goal
	 * of the verification condition with index ind
	 * 
	 */
	public int getOrigin( int ind) {
		VC vc = (VC)vcs.elementAt( ind);
		return vc.getType();
	}

	
	public String getComment(int ind) {
		VC vc = (VC)vcs.elementAt( ind);
		return vc.getComment();
	}
	
	/**
	 * checks if the formula <b>f</b> is contained already in the vector of formulas
	 * <b>v</b>
	 * @param v - a vector of formulas
	 * @param f - a formula
	 * @return
	 */
	private boolean checkIfInHypothesis(Vector v, Formula f) {
		if (v == null) {
			return false;
		}
		for (int i = 0; i < v.size(); i++) {
			Formula _f = ( (Formula)(v.elementAt( i ))) ;
			if (_f.equals( f)) {
				return true;
			}
		}
		return false;
	}
	
	
	
	public int getNumVc() {
		if (vcs == null) {
			return 0;
		}
		return vcs.size();
	}

	

    public void generateBoolConstraints( ) {
    	if (goalPool == null) {
    		return;
    	}
    	Enumeration goals = goalPool.elements();
    	while (goals.hasMoreElements()) {
        	Formula f = (Formula)goals.nextElement();
            Formula boolCond = f.generateBoolExpressionConditions();
            if (boolCond == Predicate0Ar.TRUE) {
            	continue;
            }
            Integer key = addHyp(0, boolCond);
            addHypsToVCs(key);
        }
        
    }

	/**
	 * @return  the offset of the instruction to which this verification conditions belong
	 */
	public int getInstrIndex() {
		return instrIndex;
	}

	/**
	 * @param instrIndex The instrIndex to set.
	 */
	public void setInstrIndex(int instrIndex) {
		this.instrIndex = instrIndex;
	}
	
	public Expression removeOLD() {
		if (hypPool != null ) {		
			Enumeration enumH = hypPool.elements();
			Hypothesis h = null;
			while (enumH.hasMoreElements()) {
				h = (Hypothesis)enumH.nextElement();
				Formula fh = h.getFormula();
				fh = (Formula) fh.removeOLD();
	 		}
		}
		if ( goalPool != null) {
			Enumeration enumG = goalPool.elements();
			Formula f = null;
			while (enumG.hasMoreElements()) {
				f = (Formula)enumG.nextElement();
				f = (Formula) f.removeOLD();
	 		}
		}
		return this;
	}

	
	
	
}
