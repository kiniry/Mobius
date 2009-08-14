package logs;

/**
 * 
 * @author Maciej Cielecki
 */
public class LogType {
    public final static LogType INPUT = new LogType(0, "INPUT");
    public final static LogType SUG_PARSE = new LogType(1, "SUG_PARSE");
    public final static LogType MODIFIER = new LogType(2, "MODIFIER");
    //TODO: dopiszcie tutaj swoje
	public static final LogType UI = new LogType(3, "UI");
	public static final LogType INIT = new LogType(4, "INIT");
    
    private String name;
    private int index;
    
    LogType(int index, String name) {
        this.name = name;
        this.index = index;
    }
    
    public int getIndex() {
        return index;
    }
    
    public String getName() {
        return name;
    }
}
