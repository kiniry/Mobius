package java.rmi.activation;

import java.util.Arrays;

public class ActivationGroupDesc$CommandEnvironment implements java.io.Serializable {
    private static final long serialVersionUID = 6165754737887770191L;
    private String command;
    private String[] options;
    
    public ActivationGroupDesc$CommandEnvironment(String cmdpath, String[] argv) {
        
        this.command = cmdpath;
        if (argv == null) {
            this.options = null;
        } else {
            this.options = new String[argv.length];
            System.arraycopy(argv, 0, this.options, 0, argv.length);
        }
    }
    
    public String getCommandPath() {
        return (this.command);
    }
    
    public String[] getCommandOptions() {
        return (this.options != null ? (String[])(String[])this.options.clone() : new String[0]);
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof ActivationGroupDesc$CommandEnvironment) {
            ActivationGroupDesc$CommandEnvironment env = (ActivationGroupDesc$CommandEnvironment)(ActivationGroupDesc$CommandEnvironment)obj;
            return ((command == null ? env.command == null : command.equals(env.command)) && Arrays.equals(options, env.options));
        } else {
            return false;
        }
    }
    
    public int hashCode() {
        return (command == null ? 0 : command.hashCode());
    }
}
