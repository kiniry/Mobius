package java.sql;

public class DriverPropertyInfo {
    
    public DriverPropertyInfo(String name, String value) {
        
        this.name = name;
        this.value = value;
    }
    public String name;
    public String description = null;
    public boolean required = false;
    public String value = null;
    public String[] choices = null;
}
