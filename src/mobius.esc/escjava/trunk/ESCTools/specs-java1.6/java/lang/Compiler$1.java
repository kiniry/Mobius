package java.lang;

class Compiler$1 implements java.security.PrivilegedAction {
    
    Compiler$1() {
        
    }
    
    public Object run() {
        boolean loaded = false;
        String jit = System.getProperty("java.compiler");
        if ((jit != null) && (!jit.equals("NONE")) && (!jit.equals(""))) {
            try {
                System.loadLibrary(jit);
                Compiler.access$000();
                loaded = true;
            } catch (UnsatisfiedLinkError e) {
                System.err.println("Warning: JIT compiler \"" + jit + "\" not found. Will use interpreter.");
            }
        }
        String info = System.getProperty("java.vm.info");
        if (loaded) {
            System.setProperty("java.vm.info", info + ", " + jit);
        } else {
            System.setProperty("java.vm.info", info + ", nojit");
        }
        return null;
    }
}
