package java.rmi.activation;

import java.rmi.MarshalledObject;
import java.util.Properties;

public final class ActivationGroupDesc implements java.io.Serializable {
    private String className;
    private String location;
    private MarshalledObject data;
    private ActivationGroupDesc$CommandEnvironment env;
    private Properties props;
    private static final long serialVersionUID = -4936225423168276595L;
    
    public ActivationGroupDesc(Properties overrides, ActivationGroupDesc$CommandEnvironment cmd) {
        this(null, null, null, overrides, cmd);
    }
    
    public ActivationGroupDesc(String className, String location, MarshalledObject data, Properties overrides, ActivationGroupDesc$CommandEnvironment cmd) {
        
        this.props = overrides;
        this.env = cmd;
        this.data = data;
        this.location = location;
        this.className = className;
    }
    
    public String getClassName() {
        return className;
    }
    
    public String getLocation() {
        return location;
    }
    
    public MarshalledObject getData() {
        return data;
    }
    
    public Properties getPropertyOverrides() {
        return (props != null) ? (Properties)(Properties)props.clone() : null;
    }
    
    public ActivationGroupDesc$CommandEnvironment getCommandEnvironment() {
        return this.env;
    }
    {
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof ActivationGroupDesc) {
            ActivationGroupDesc desc = (ActivationGroupDesc)(ActivationGroupDesc)obj;
            return ((className == null ? desc.className == null : className.equals(desc.className)) && (location == null ? desc.location == null : location.equals(desc.location)) && (data == null ? desc.data == null : data.equals(desc.data)) && (env == null ? desc.env == null : env.equals(desc.env)) && (props == null ? desc.props == null : props.equals(desc.props)));
        } else {
            return false;
        }
    }
    
    public int hashCode() {
        return ((location == null ? 0 : location.hashCode() << 24) ^ (env == null ? 0 : env.hashCode() << 16) ^ (className == null ? 0 : className.hashCode() << 8) ^ (data == null ? 0 : data.hashCode()));
    }
}
