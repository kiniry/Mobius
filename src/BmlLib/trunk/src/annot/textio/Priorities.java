package annot.textio;

import annot.io.Code;

public abstract class Priorities implements Code {

	private static int[] priorities;

	public static final int LEAF = 0;

	private static void setPrioritues() {
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

	public static int getPriority(int opcode) {
		if (priorities == null)
			setPrioritues();
		if (opcode > 255)
			throw new RuntimeException("invalid opcode: " + opcode);
		if (priorities[opcode] == -1) {
			throw new RuntimeException("invalid opcode: " + opcode);
		}
		return priorities[opcode];
	}

}
