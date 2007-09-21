package annot.textio;

import annot.io.Code;

/**
 * This class contains priorities of all expression types.
 * 
 * @author tomekb
 */
public abstract class Priorities implements Code {

	/**
	 * Expression's priority array, from expression's type
	 * (connector, from {@link Code} interface) to it's
	 * priority.
	 */
	private static int[] priorities;

	/**
	 * Priority of expressions that have no subexpressions.
	 */
	public static final int LEAF = 0;

	/**
	 * Initializes <code>priorities</code> array.
	 */
	private static void setPriorities() {
		priorities = new int[255];
		for (int i = 0; i < 255; i++)
			priorities[i] = -1;
		priorities[NOT] = 3;
		priorities[LESS] = 7;
		priorities[LESSEQ] = 7;
		priorities[GRT] = 7;
		priorities[GRTEQ] = 7;
		priorities[EQ] = 8;
		priorities[NOTEQ] = 8;
		priorities[AND] = 12;
		priorities[OR] = 13;
		priorities[IMPLIES] = 14;
		priorities[EQUIV] = 15;
		priorities[NOTEQUIV] = 15;
		// ?
		priorities[FORALL] = 17;
		priorities[EXISTS] = 17;
		priorities[FORALL_WITH_NAME] = 17;
		priorities[EXISTS_WITH_NAME] = 17;
	}

	/**
	 * Returns priority of expression with given type
	 * (connector). Sets all priorities at first call.
	 * 
	 * @param opcode - expression type (connector), from
	 * 		{@link Code} interface.
	 * @return Priority of expressions of given type.
	 */
	public static int getPriority(int opcode) {
		if (priorities == null)
			setPriorities();
		if (opcode > 255)
			throw new RuntimeException("invalid opcode: " + opcode);
		if (priorities[opcode] == -1) {
			throw new RuntimeException("invalid opcode: " + opcode);
		}
		return priorities[opcode];
	}

}
