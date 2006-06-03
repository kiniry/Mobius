package bytecode_wp.vcg;

import java.util.Vector;

import bytecode_wp.formula.Formula;

public class Goal {
	private Formula goal;
	
	
	public Goal(Formula f) {
		goal = f;
	}
	
	
	/**
	 * 
	 * @return
	 */
	public Vector getGoalsInConj() {
		
			return goal.elimConj();
		
		
	}

}
