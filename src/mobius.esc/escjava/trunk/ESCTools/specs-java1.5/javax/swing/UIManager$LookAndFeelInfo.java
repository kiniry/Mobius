package javax.swing;

public class UIManager$LookAndFeelInfo {
    private String name;
    private String className;
    
    public UIManager$LookAndFeelInfo(String name, String className) {
        
        this.name = name;
        this.className = className;
    }
    
    public String getName() {
        return name;
    }
    
    public String getClassName() {
        return className;
    }
    
    public String toString() {
        return getClass().getName() + "[" + getName() + " " + getClassName() + "]";
    }
}
