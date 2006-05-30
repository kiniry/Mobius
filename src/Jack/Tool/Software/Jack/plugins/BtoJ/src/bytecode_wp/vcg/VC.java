package bytecode_wp.vcg;

import java.util.Vector;

import bytecode_wp.bcexpression.Expression;
import bytecode_wp.formula.Connector;
import bytecode_wp.formula.Formula;
import bytecode_wp.formula.Predicate0Ar;
import bytecode_wp.formula.Predicate2Ar;

public class VC {
	// references to the hypothesis
	private Vector hyps;

	private Integer goal;

	//comment about the goal - e.g. the method for which the requires is proven
	private String comment = "";
	/**
	 * the type of this vc
	 * 
	 */
	private byte type;

	public VC(byte type, Integer goalId) {
		this.goal = goalId;
		this.type = type;

	}

	/**
	 * this constructor is used when for copying the object
	 * 
	 * @param type
	 * @param goal
	 * @param hyps
	 */
	public VC(byte type, Integer goalId, Vector hyps) {
		this.goal = goalId;
		this.type = type;
		this.hyps = hyps;

	}

	/**
	 * this constructor is used when for copying the object
	 * 
	 * @param type
	 * @param goal
	 * @param hyps
	 */
	public VC(byte type, Integer goalId, Integer hypId) {
		this.goal = goalId;
		this.type = type;
		addHyp(hypId);

	}

	public void addHyp(Integer hypId) {
		if (hypId == VCGPath.TRUE_AS_HYPOTHESIS) {
			return;
		}
		initHyp();
		// if this id is already in the vector
		// of hypothesis indexes then do not add it
		if (hyps.contains( hypId)) {
			return ;
		}
		hyps.add(hypId);
	}


	

	/**
	 * this method is used when a copy of this object is made
	 * 
	 * @param id - the old id of the hypothesis in the original object 
	 * @param newId - the new id of the hypothesis
	 */
	protected void changeHypKeys(Integer id, Integer newId) {
		if (hyps == null) {
			return;
		}
		int ind = hyps.indexOf(id);
		if (ind == -1) {
			return ;
		}
		hyps.remove( ind);
		hyps.insertElementAt( newId, ind);

	}
	
	protected void changeGoalKeys(Integer id, Integer newId) {
		if (goal != id) {
			return;
		}
		goal = newId;
	}
	

	private void initHyp() {

		if (hyps == null) {
			hyps = new Vector();

		}
	}

	public byte getType() {
		return type;
	}

	public Vector getHyps() {
		return hyps;
	}

	public Integer getGoal() {
		return goal;
	}

	public VC copy() {
		Vector hypCopy = (hyps !=null)? (Vector) hyps.clone() : null;
		return new VC(type, goal, hypCopy);
	}

	public String getComment() {
		return comment;
	}
}
