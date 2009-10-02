package java.lang;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public final class ProcessBuilder {
    /*synthetic*/ static final boolean $assertionsDisabled = !ProcessBuilder.class.desiredAssertionStatus();
    private List command;
    private File directory;
    private Map environment;
    private boolean redirectErrorStream;
    
    public ProcessBuilder(List command) {
        
        if (command == null) throw new NullPointerException();
        this.command = command;
    }
    
    public ProcessBuilder(String... command) {
        
        this.command = new ArrayList(command.length);
        for (String[] arr$ = command, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            String arg = arr$[i$];
            this.command.add(arg);
        }
    }
    
    public ProcessBuilder command(List command) {
        if (command == null) throw new NullPointerException();
        this.command = command;
        return this;
    }
    
    public ProcessBuilder command(String... command) {
        this.command = new ArrayList(command.length);
        for (String[] arr$ = command, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            String arg = arr$[i$];
            this.command.add(arg);
        }
        return this;
    }
    
    public List command() {
        return command;
    }
    
    public Map environment() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) security.checkPermission(new RuntimePermission("getenv.*"));
        if (environment == null) environment = ProcessEnvironment.environment();
        if (!$assertionsDisabled && !(environment != null)) throw new AssertionError();
        return environment;
    }
    
    ProcessBuilder environment(String[] envp) {
        if (!$assertionsDisabled && !(environment == null)) throw new AssertionError();
        if (envp != null) {
            environment = ProcessEnvironment.emptyEnvironment(envp.length);
            if (!$assertionsDisabled && !(environment != null)) throw new AssertionError();
            for (String[] arr$ = envp, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                String envstring = arr$[i$];
                {
                    if (envstring.indexOf((int)'\000') != -1) envstring = envstring.replaceFirst("\000.*", "");
                    int eqlsign = envstring.indexOf('=', ProcessEnvironment.MIN_NAME_LENGTH);
                    if (eqlsign != -1) environment.put(envstring.substring(0, eqlsign), envstring.substring(eqlsign + 1));
                }
            }
        }
        return this;
    }
    
    public File directory() {
        return directory;
    }
    
    public ProcessBuilder directory(File directory) {
        this.directory = directory;
        return this;
    }
    
    public boolean redirectErrorStream() {
        return redirectErrorStream;
    }
    
    public ProcessBuilder redirectErrorStream(boolean redirectErrorStream) {
        this.redirectErrorStream = redirectErrorStream;
        return this;
    }
    
    public Process start() throws IOException {
        String[] cmdarray = (String[])command.toArray(new String[command.size()]);
        for (String[] arr$ = cmdarray, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            String arg = arr$[i$];
            if (arg == null) throw new NullPointerException();
        }
        String prog = cmdarray[0];
        SecurityManager security = System.getSecurityManager();
        if (security != null) security.checkExec(prog);
        String dir = directory == null ? null : directory.toString();
        return ProcessImpl.start(cmdarray, environment, dir, redirectErrorStream);
    }
}
