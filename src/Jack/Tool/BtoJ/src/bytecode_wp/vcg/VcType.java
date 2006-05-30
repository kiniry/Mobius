package bytecode_wp.vcg;

import jml2b.pog.lemma.GoalOrigin;

public interface VcType {
	
	public static final byte NORM_POST = GoalOrigin.ENSURES;
	public static final byte INSTR_THROW_EXC = GoalOrigin.EXSURES;
	public static final byte LOOPINIT = GoalOrigin.LOOP_INVARIANT_INIT;
	public static final byte LOOPPRESERV = GoalOrigin.LOOP_INVARIANT_PRESERVE;

	public static final byte ASSERTION = GoalOrigin.ASSERT;
	public static final byte PRE_METH_CALL = GoalOrigin.REQUIRES;
	
	public static final byte  LOOP_TERMINATION = GoalOrigin.LOOP_VARIANT;
	

	public static final byte INSTANCE_INVARIANT =GoalOrigin.MEMBER_INVARIANT ;
	public static final byte STATIC_INVARIANT = GoalOrigin.STATIC_INVARIANT ;
	public static final byte HISTORY_CONSTR = GoalOrigin.INSTANCE_CONSTRAINT;

	public static final byte MODIFIES = GoalOrigin.MODIFIES;

	


}