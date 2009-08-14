package logs;

import java.util.BitSet;

/**
 * 
 * @author Maciej Cielecki
 */
public class Log {
    private static BitSet status = new BitSet();
    
    static {
        //Nie wiem czy to dobre rozwiazanie
        //ale tutaj mozna sobie powlaczac i wylaczac co ma byc logowane
        Log.setEnabled(LogType.INPUT, false);
        Log.setEnabled(LogType.SUG_PARSE, false);
        Log.setEnabled(LogType.UI, true);
        Log.setEnabled(LogType.MODIFIER, true);
    	Log.setEnabled(LogType.INIT, false);
	}
    
    public static void setEnabled(LogType type, boolean enabled) {
        status.set(type.getIndex(), enabled);
    }
    
    public static void println(LogType type, String string) {
        if (status.get(type.getIndex())) {
            System.out.println(type.getName() + ": " + string);
        }
    }
}

