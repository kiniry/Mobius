package java.util.logging;

public interface Filter {
    
    public boolean isLoggable(LogRecord record);
}
