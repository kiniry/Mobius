package annot.bcclass;

public class MLog implements IMessageLog {

	public static int mask = PNORMAL;

	public static void putMsg(int priority, String msg) {
		if ((priority & mask) > 0)
			System.out.println(msg);
	}

}
