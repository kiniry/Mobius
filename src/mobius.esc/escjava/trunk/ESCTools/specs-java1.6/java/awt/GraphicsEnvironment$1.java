package java.awt;

class GraphicsEnvironment$1 implements java.security.PrivilegedAction {
    
    GraphicsEnvironment$1() {
        
    }
    
    public Object run() {
        String nm = System.getProperty("java.awt.headless");
        if (nm == null) {
            if (System.getProperty("javaplugin.version") != null) {
                GraphicsEnvironment.access$002(GraphicsEnvironment.access$102(Boolean.FALSE));
            } else {
                String osName = System.getProperty("os.name");
                GraphicsEnvironment.access$002(GraphicsEnvironment.access$102(Boolean.valueOf(("Linux".equals(osName) || "SunOS".equals(osName)) && (System.getenv("DISPLAY") == null))));
            }
        } else if (nm.equals("true")) {
            GraphicsEnvironment.access$002(Boolean.TRUE);
        } else {
            GraphicsEnvironment.access$002(Boolean.FALSE);
        }
        return null;
    }
}
