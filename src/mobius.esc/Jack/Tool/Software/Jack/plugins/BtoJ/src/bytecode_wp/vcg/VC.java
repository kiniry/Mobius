package bytecode_wp.vcg;

import java.util.Vector;

public class VC {
	// references to the hypothesis
	private Vector hyps;

	private Integer goal;

	/** the offset of the instruction to which this verification condition refers */ 
	private int position = -1;
	
	/**comment about the goal - e.g.: " the method for which the requires is proven"*/
	private String comment = "";
	/**
	 * the type of this vc
	 * 
	 */
	private byte type;

	private String exc = null;

	public VC(byte type, Integer goalId) {
		this.goal = goalId;
		this.type = type;

	}
	
	public VC(byte type, Integer goalId, int position) {
		this( type, goalId);
		this.position = position;
		
	}

	public VC(byte type, Integer goalId, String exc) {
		this( type, goalId);
		this.exc  = exc;
	}

	/**
	 * this constructor is used when for copying the object
	 * 
	 * @param type
	 * @param goal
	 * @param hyps
	 */
	public VC(byte type, Integer goalId, Integer hypId) {
		this( type, goalId);
		addHyp(hypId);

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

	public int getPosition() {
		return position;
	}

	public String getExc() {
		return exc;
	}

}
