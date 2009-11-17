package javax.sound.sampled;

public class Mixer$Info {
    private String name;
    private String vendor;
    private String description;
    private String version;
    
    protected Mixer$Info(String name, String vendor, String description, String version) {
        
        this.name = name;
        this.vendor = vendor;
        this.description = description;
        this.version = version;
    }
    
    public final boolean equals(Object obj) {
        return super.equals(obj);
    }
    
    public final int hashCode() {
        return super.hashCode();
    }
    
    public final String getName() {
        return name;
    }
    
    public final String getVendor() {
        return vendor;
    }
    
    public final String getDescription() {
        return description;
    }
    
    public final String getVersion() {
        return version;
    }
    
    public final String toString() {
        return (name + ", version " + version);
    }
}
