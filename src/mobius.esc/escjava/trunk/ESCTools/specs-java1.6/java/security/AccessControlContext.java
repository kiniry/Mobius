package java.security;

import java.util.ArrayList;
import java.util.List;
import sun.security.util.Debug;
import sun.security.util.SecurityConstants;

public final class AccessControlContext {
    private ProtectionDomain[] context;
    private boolean isPrivileged;
    private AccessControlContext privilegedContext;
    private DomainCombiner combiner = null;
    private static boolean debugInit = false;
    private static Debug debug = null;
    
    static Debug getDebug() {
        if (debugInit) return debug; else {
            if (Policy.isSet()) {
                debug = Debug.getInstance("access");
                debugInit = true;
            }
            return debug;
        }
    }
    
    public AccessControlContext(ProtectionDomain[] context) {
        
        if (context.length == 0) {
            this.context = null;
        } else if (context.length == 1) {
            if (context[0] != null) {
                this.context = (ProtectionDomain[])(ProtectionDomain[])context.clone();
            } else {
                this.context = null;
            }
        } else {
            List v = new ArrayList(context.length);
            for (int i = 0; i < context.length; i++) {
                if ((context[i] != null) && (!v.contains(context[i]))) v.add(context[i]);
            }
            this.context = new ProtectionDomain[v.size()];
            this.context = (ProtectionDomain[])(ProtectionDomain[])v.toArray(this.context);
        }
    }
    
    public AccessControlContext(AccessControlContext acc, DomainCombiner combiner) {
        
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.CREATE_ACC_PERMISSION);
        }
        this.context = acc.context;
        this.combiner = combiner;
    }
    
    AccessControlContext(ProtectionDomain[] context, boolean isPrivileged) {
        
        this.context = context;
        this.isPrivileged = isPrivileged;
    }
    
    boolean isPrivileged() {
        return isPrivileged;
    }
    
    public DomainCombiner getDomainCombiner() {
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.GET_COMBINER_PERMISSION);
        }
        return combiner;
    }
    
    public void checkPermission(Permission perm) throws AccessControlException {
        if (perm == null) {
            throw new NullPointerException("permission can\'t be null");
        }
        if (getDebug() != null) {
            if (Debug.isOn("stack")) Thread.currentThread().dumpStack();
            if (Debug.isOn("domain")) {
                if (context == null) {
                    debug.println("domain (context is null)");
                } else {
                    for (int i = 0; i < context.length; i++) {
                        debug.println("domain " + i + " " + context[i]);
                    }
                }
            }
        }
        if (context == null) return;
        for (int i = 0; i < context.length; i++) {
            if (context[i] != null && !context[i].implies(perm)) {
                if (debug != null) {
                    debug.println("access denied " + perm);
                    if (Debug.isOn("failure")) {
                        Thread.currentThread().dumpStack();
                        final ProtectionDomain pd = context[i];
                        final Debug db = debug;
                        AccessController.doPrivileged(new AccessControlContext$1(this, db, pd));
                    }
                }
                throw new AccessControlException("access denied " + perm, perm);
            }
        }
        if (debug != null) debug.println("access allowed " + perm);
        return;
    }
    
    AccessControlContext optimize() {
        AccessControlContext acc;
        if (isPrivileged) {
            acc = privilegedContext;
        } else {
            acc = AccessController.getInheritedAccessControlContext();
        }
        boolean skipStack = (context == null);
        boolean skipAssigned = (acc == null || acc.context == null);
        if (skipAssigned && skipStack) {
            return (acc != null) ? acc : this;
        }
        if (acc != null && acc.combiner != null) {
            return goCombiner(context, acc);
        }
        if (skipStack) {
            return acc;
        }
        int slen = context.length;
        if (skipAssigned && slen <= 2) {
            return this;
        }
        if ((slen == 1) && (context[0] == acc.context[0])) {
            return acc;
        }
        int n = (skipAssigned) ? 0 : acc.context.length;
        ProtectionDomain[] pd = new ProtectionDomain[slen + n];
        if (!skipAssigned) {
            System.arraycopy(acc.context, 0, pd, 0, n);
        }
        outer: for (int i = 0; i < context.length; i++) {
            ProtectionDomain sd = context[i];
            if (sd != null) {
                for (int j = 0; j < n; j++) {
                    if (sd == pd[j]) {
                        continue outer;
                    }
                }
                pd[n++] = sd;
            }
        }
        if (n != pd.length) {
            if (!skipAssigned && n == acc.context.length) {
                return acc;
            } else if (skipAssigned && n == slen) {
                return this;
            }
            ProtectionDomain[] tmp = new ProtectionDomain[n];
            System.arraycopy(pd, 0, tmp, 0, n);
            pd = tmp;
        }
        this.context = pd;
        this.combiner = null;
        this.isPrivileged = false;
        return this;
    }
    
    private AccessControlContext goCombiner(ProtectionDomain[] current, AccessControlContext assigned) {
        if (getDebug() != null) {
            debug.println("AccessControlContext invoking the Combiner");
        }
        ProtectionDomain[] combinedPds = assigned.combiner.combine(current, assigned.context);
        this.context = combinedPds;
        this.combiner = assigned.combiner;
        this.isPrivileged = false;
        return this;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof AccessControlContext)) return false;
        AccessControlContext that = (AccessControlContext)(AccessControlContext)obj;
        if (context == null) {
            return (that.context == null);
        }
        if (that.context == null) return false;
        if (!(this.containsAllPDs(that) && that.containsAllPDs(this))) return false;
        if (this.combiner == null) return (that.combiner == null);
        if (that.combiner == null) return false;
        if (!this.combiner.equals(that.combiner)) return false;
        return true;
    }
    
    private boolean containsAllPDs(AccessControlContext that) {
        boolean match = false;
        ProtectionDomain thisPd;
        for (int i = 0; i < context.length; i++) {
            match = false;
            if ((thisPd = context[i]) == null) {
                for (int j = 0; (j < that.context.length) && !match; j++) {
                    match = (that.context[j] == null);
                }
            } else {
                Class thisPdClass = thisPd.getClass();
                ProtectionDomain thatPd;
                for (int j = 0; (j < that.context.length) && !match; j++) {
                    thatPd = that.context[j];
                    match = (thatPd != null && thisPdClass == thatPd.getClass() && thisPd.equals(thatPd));
                }
            }
            if (!match) return false;
        }
        return match;
    }
    
    public int hashCode() {
        int hashCode = 0;
        if (context == null) return hashCode;
        for (int i = 0; i < context.length; i++) {
            if (context[i] != null) hashCode ^= context[i].hashCode();
        }
        return hashCode;
    }
}
