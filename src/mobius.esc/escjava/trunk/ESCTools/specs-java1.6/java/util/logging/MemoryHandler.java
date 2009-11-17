package java.util.logging;

public class MemoryHandler extends Handler {
    private static final int DEFAULT_SIZE = 1000;
    private Level pushLevel;
    private int size;
    private Handler target;
    private LogRecord[] buffer;
    int start;
    int count;
    
    private void configure() {
        LogManager manager = LogManager.getLogManager();
        String cname = getClass().getName();
        pushLevel = manager.getLevelProperty(cname + ".push", Level.SEVERE);
        size = manager.getIntProperty(cname + ".size", DEFAULT_SIZE);
        if (size <= 0) {
            size = DEFAULT_SIZE;
        }
        setLevel(manager.getLevelProperty(cname + ".level", Level.ALL));
        setFilter(manager.getFilterProperty(cname + ".filter", null));
        setFormatter(manager.getFormatterProperty(cname + ".formatter", new SimpleFormatter()));
    }
    
    public MemoryHandler() {
        
        sealed = false;
        configure();
        sealed = true;
        String name = "???";
        try {
            LogManager manager = LogManager.getLogManager();
            name = manager.getProperty("java.util.logging.MemoryHandler.target");
            Class clz = ClassLoader.getSystemClassLoader().loadClass(name);
            target = (Handler)(Handler)clz.newInstance();
        } catch (Exception ex) {
            throw new RuntimeException("MemoryHandler can\'t load handler \"" + name + "\"", ex);
        }
        init();
    }
    
    private void init() {
        buffer = new LogRecord[size];
        start = 0;
        count = 0;
    }
    
    public MemoryHandler(Handler target, int size, Level pushLevel) {
        
        if (target == null || pushLevel == null) {
            throw new NullPointerException();
        }
        if (size <= 0) {
            throw new IllegalArgumentException();
        }
        sealed = false;
        configure();
        sealed = true;
        this.target = target;
        this.pushLevel = pushLevel;
        this.size = size;
        init();
    }
    
    public synchronized void publish(LogRecord record) {
        if (!isLoggable(record)) {
            return;
        }
        int ix = (start + count) % buffer.length;
        buffer[ix] = record;
        if (count < buffer.length) {
            count++;
        } else {
            start++;
        }
        if (record.getLevel().intValue() >= pushLevel.intValue()) {
            push();
        }
    }
    
    public synchronized void push() {
        for (int i = 0; i < count; i++) {
            int ix = (start + i) % buffer.length;
            LogRecord record = buffer[ix];
            target.publish(record);
        }
        start = 0;
        count = 0;
    }
    
    public void flush() {
        target.flush();
    }
    
    public void close() throws SecurityException {
        target.close();
        setLevel(Level.OFF);
    }
    
    public void setPushLevel(Level newLevel) throws SecurityException {
        if (newLevel == null) {
            throw new NullPointerException();
        }
        LogManager manager = LogManager.getLogManager();
        checkAccess();
        pushLevel = newLevel;
    }
    
    public synchronized Level getPushLevel() {
        return pushLevel;
    }
    
    public boolean isLoggable(LogRecord record) {
        return super.isLoggable(record);
    }
}
