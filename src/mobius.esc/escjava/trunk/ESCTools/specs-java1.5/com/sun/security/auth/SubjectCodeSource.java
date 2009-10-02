package com.sun.security.auth;

import java.net.URL;
import java.util.*;
import java.security.CodeSource;
import java.security.Principal;
import java.security.cert.Certificate;
import java.lang.reflect.Constructor;
import javax.security.auth.Subject;

class SubjectCodeSource extends CodeSource implements java.io.Serializable {
    private static final long serialVersionUID = 6039418085604715275L;
    private static final java.util.ResourceBundle rb = (java.util.ResourceBundle)(ResourceBundle)java.security.AccessController.doPrivileged(new SubjectCodeSource$1());
    private Subject subject;
    private LinkedList principals;
    private static final Class[] PARAMS = {String.class};
    private static final sun.security.util.Debug debug = sun.security.util.Debug.getInstance("auth", "\t[Auth Access]");
    private ClassLoader sysClassLoader;
    
    SubjectCodeSource(Subject subject, LinkedList principals, URL url, Certificate[] certs) {
        super(url, certs);
        this.subject = subject;
        this.principals = (principals == null ? new LinkedList() : new LinkedList(principals));
        sysClassLoader = (ClassLoader)(ClassLoader)java.security.AccessController.doPrivileged(new SubjectCodeSource$2(this));
    }
    
    LinkedList getPrincipals() {
        return principals;
    }
    
    Subject getSubject() {
        return subject;
    }
    
    public boolean implies(CodeSource codesource) {
        LinkedList subjectList = null;
        if (codesource == null || !(codesource instanceof SubjectCodeSource) || !(super.implies(codesource))) {
            if (debug != null) debug.println("\tSubjectCodeSource.implies: FAILURE 1");
            return false;
        }
        SubjectCodeSource that = (SubjectCodeSource)(SubjectCodeSource)codesource;
        if (this.principals == null) {
            if (debug != null) debug.println("\tSubjectCodeSource.implies: PASS 1");
            return true;
        }
        if (that.getSubject() == null || that.getSubject().getPrincipals().size() == 0) {
            if (debug != null) debug.println("\tSubjectCodeSource.implies: FAILURE 2");
            return false;
        }
        ListIterator li = this.principals.listIterator(0);
        while (li.hasNext()) {
            PolicyParser$PrincipalEntry pppe = (PolicyParser$PrincipalEntry)(PolicyParser$PrincipalEntry)li.next();
            try {
                Class principalComparator = Class.forName(pppe.principalClass, true, sysClassLoader);
                Constructor c = principalComparator.getConstructor(PARAMS);
                PrincipalComparator pc = (PrincipalComparator)(PrincipalComparator)c.newInstance(new Object[]{pppe.principalName});
                if (!pc.implies(that.getSubject())) {
                    if (debug != null) debug.println("\tSubjectCodeSource.implies: FAILURE 3");
                    return false;
                } else {
                    if (debug != null) debug.println("\tSubjectCodeSource.implies: PASS 2");
                    return true;
                }
            } catch (Exception e) {
                if (subjectList == null) {
                    if (that.getSubject() == null) {
                        if (debug != null) debug.println("\tSubjectCodeSource.implies: FAILURE 4");
                        return false;
                    }
                    Iterator i = that.getSubject().getPrincipals().iterator();
                    subjectList = new LinkedList();
                    while (i.hasNext()) {
                        Principal p = (Principal)(Principal)i.next();
                        PolicyParser$PrincipalEntry spppe = new PolicyParser$PrincipalEntry(p.getClass().getName(), p.getName());
                        subjectList.add(spppe);
                    }
                }
                if (!subjectListImpliesPrincipalEntry(subjectList, pppe)) {
                    if (debug != null) debug.println("\tSubjectCodeSource.implies: FAILURE 5");
                    return false;
                }
            }
        }
        if (debug != null) debug.println("\tSubjectCodeSource.implies: PASS 3");
        return true;
    }
    
    private boolean subjectListImpliesPrincipalEntry(LinkedList subjectList, PolicyParser$PrincipalEntry pppe) {
        ListIterator li = subjectList.listIterator(0);
        while (li.hasNext()) {
            PolicyParser$PrincipalEntry listPppe = (PolicyParser$PrincipalEntry)(PolicyParser$PrincipalEntry)li.next();
            if (pppe.principalClass.equals(PolicyParser$PrincipalEntry.WILDCARD_CLASS) || pppe.principalClass.equals(listPppe.principalClass)) {
                if (pppe.principalName.equals(PolicyParser$PrincipalEntry.WILDCARD_NAME) || pppe.principalName.equals(listPppe.principalName)) return true;
            }
        }
        return false;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (super.equals(obj) == false) return false;
        if (!(obj instanceof SubjectCodeSource)) return false;
        SubjectCodeSource that = (SubjectCodeSource)(SubjectCodeSource)obj;
        try {
            if (this.getSubject() != that.getSubject()) return false;
        } catch (SecurityException se) {
            return false;
        }
        if ((this.principals == null && that.principals != null) || (this.principals != null && that.principals == null)) return false;
        if (this.principals != null && that.principals != null) {
            if (!this.principals.containsAll(that.principals) || !that.principals.containsAll(this.principals)) return false;
        }
        return true;
    }
    
    public int hashCode() {
        return super.hashCode();
    }
    
    public String toString() {
        String returnMe = super.toString();
        if (getSubject() != null) {
            if (debug != null) {
                final Subject finalSubject = getSubject();
                returnMe = returnMe + "\n" + java.security.AccessController.doPrivileged(new SubjectCodeSource$3(this, finalSubject));
            } else {
                returnMe = returnMe + "\n" + getSubject().toString();
            }
        }
        if (principals != null) {
            ListIterator li = principals.listIterator();
            while (li.hasNext()) {
                PolicyParser$PrincipalEntry pppe = (PolicyParser$PrincipalEntry)(PolicyParser$PrincipalEntry)li.next();
                returnMe = returnMe + rb.getString("\n") + pppe.principalClass + " " + pppe.principalName;
            }
        }
        return returnMe;
    }
}
