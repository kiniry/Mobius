package com.sun.jmx.mbeanserver;

import java.util.Hashtable;
import java.util.Enumeration;
import java.util.Set;
import java.util.ArrayList;
import java.util.HashSet;
import javax.management.*;
import com.sun.jmx.defaults.ServiceName;
import com.sun.jmx.trace.Trace;

public class RepositorySupport implements Repository {
    private static final ObjectName _WholeWordQueryObjectName;
    static {
        try {
            _WholeWordQueryObjectName = new ObjectName("*:*");
        } catch (MalformedObjectNameException e) {
            throw new UnsupportedOperationException(e.getMessage());
        }
    }
    private static int _slen;
    private static int _plen;
    private final Hashtable domainTb;
    private int nbElements = 0;
    private final String domain;
    private static final String dbgTag = "Repository";
    
    private static final boolean isTraceOn() {
        return Trace.isSelected(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER);
    }
    
    private static final void trace(String clz, String func, String info) {
        Trace.send(Trace.LEVEL_TRACE, Trace.INFO_MBEANSERVER, clz, func, info);
    }
    
    private static final void trace(String func, String info) {
        trace(dbgTag, func, info);
    }
    
    private static final boolean isDebugOn() {
        return Trace.isSelected(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER);
    }
    
    private static final void debug(String clz, String func, String info) {
        Trace.send(Trace.LEVEL_DEBUG, Trace.INFO_MBEANSERVER, clz, func, info);
    }
    
    private static final void debug(String func, String info) {
        debug(dbgTag, func, info);
    }
    {
    }
    
    private final void addAllMatching(final Hashtable moiTb, final Set result, final RepositorySupport$ObjectNamePattern pattern) {
        synchronized (moiTb) {
            for (Enumeration e = moiTb.elements(); e.hasMoreElements(); ) {
                final NamedObject no = (NamedObject)(NamedObject)e.nextElement();
                final ObjectName on = no.getName();
                if (pattern.matchKeys(on)) result.add(no);
            }
        }
    }
    
    private final void addNewDomMoi(final Object object, final String dom, final ObjectName name) {
        final Hashtable moiTb = new Hashtable();
        domainTb.put(dom, moiTb);
        moiTb.put(name.getCanonicalKeyPropertyListString(), new NamedObject(name, object));
        nbElements++;
    }
    
    private static boolean wildmatch(char[] s, char[] p, int si, int pi) {
        char c;
        _slen = s.length;
        _plen = p.length;
        while (pi < _plen) {
            c = p[pi++];
            if (c == '?') {
                if (++si > _slen) return false;
            } else if (c == '*') {
                if (pi >= _plen) return true;
                do {
                    if (wildmatch(s, p, si, pi)) return true;
                }                 while (++si < _slen);
                return false;
            } else {
                if (si >= _slen || c != s[si++]) return false;
            }
        }
        return (si == _slen);
    }
    
    private NamedObject retrieveNamedObject(ObjectName name) {
        if (name.isPattern() == true) return null;
        String dom = name.getDomain().intern();
        if (dom.length() == 0) {
            dom = domain;
        }
        Object tmp_object = domainTb.get(dom);
        if (tmp_object == null) {
            return null;
        }
        Hashtable moiTb = (Hashtable)(Hashtable)tmp_object;
        Object o = moiTb.get(name.getCanonicalKeyPropertyListString());
        if (o != null) {
            return (NamedObject)(NamedObject)o;
        } else return null;
    }
    
    public RepositorySupport(String domain) {
        
        domainTb = new Hashtable(5);
        if (domain != null && domain.length() != 0) this.domain = domain; else this.domain = ServiceName.DOMAIN;
        domainTb.put(this.domain.intern(), new Hashtable());
    }
    
    public void setConfigParameters(ArrayList configParameters) {
        return;
    }
    
    public String[] getDomains() {
        final ArrayList result;
        synchronized (domainTb) {
            result = new ArrayList(domainTb.size());
            for (Enumeration e = domainTb.keys(); e.hasMoreElements(); ) {
                final String key = (String)(String)e.nextElement();
                if (key == null) continue;
                final Hashtable t = (Hashtable)(Hashtable)domainTb.get(key);
                if (t == null || t.size() == 0) continue;
                result.add(key);
            }
        }
        return (String[])(String[])result.toArray(new String[result.size()]);
    }
    
    public boolean isFiltering() {
        return false;
    }
    
    public void addMBean(final Object object, ObjectName name) throws InstanceAlreadyExistsException {
        if (isTraceOn()) {
            trace("addMBean", "name=" + name);
        }
        String dom = name.getDomain().intern();
        boolean to_default_domain = false;
        if (dom.length() == 0) {
            try {
                name = new ObjectName(domain + name.toString());
            } catch (MalformedObjectNameException e) {
                if (isDebugOn()) {
                    debug("addMBean", "Unexpected MalformedObjectNameException");
                }
            }
        }
        if (dom == domain) {
            to_default_domain = true;
            dom = domain;
        } else {
            to_default_domain = false;
        }
        if (name.isPattern() == true) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Repository: cannot add mbean for pattern name " + name.toString()));
        }
        if (!to_default_domain && dom.equals("JMImplementation") && domainTb.containsKey("JMImplementation")) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Repository: domain name cannot be JMImplementation"));
        }
        final Hashtable moiTb = (Hashtable)(Hashtable)domainTb.get(dom);
        if (moiTb == null) {
            addNewDomMoi(object, dom, name);
            return;
        } else {
            String cstr = name.getCanonicalKeyPropertyListString();
            Object elmt = moiTb.get(cstr);
            if (elmt != null) {
                throw new InstanceAlreadyExistsException(name.toString());
            } else {
                nbElements++;
                moiTb.put(cstr, new NamedObject(name, object));
            }
        }
    }
    
    public boolean contains(ObjectName name) {
        if (isTraceOn()) {
            trace("contains", "name=" + name);
        }
        return (retrieveNamedObject(name) != null);
    }
    
    public Object retrieve(ObjectName name) {
        if (isTraceOn()) {
            trace("retrieve", "name=" + name);
        }
        NamedObject no = retrieveNamedObject(name);
        if (no == null) return null; else return no.getObject();
    }
    
    public Set query(ObjectName pattern, QueryExp query) {
        RepositorySupport$ObjectNamePattern on_pattern = null;
        final HashSet result = new HashSet();
        ObjectName name = null;
        if (pattern == null || pattern.getCanonicalName().length() == 0 || pattern.equals(_WholeWordQueryObjectName)) name = _WholeWordQueryObjectName; else name = pattern;
        if (!name.isPattern()) {
            final NamedObject no = retrieveNamedObject(name);
            if (no != null) result.add(no);
            return result;
        }
        if (name == _WholeWordQueryObjectName) {
            synchronized (domainTb) {
                for (final Enumeration e = domainTb.elements(); e.hasMoreElements(); ) {
                    final Hashtable moiTb = (Hashtable)(Hashtable)e.nextElement();
                    result.addAll(moiTb.values());
                }
            }
            return result;
        }
        String canonical_key_property_list_string = name.getCanonicalKeyPropertyListString();
        if (name.getDomain().length() == 0) {
            final Hashtable moiTb = (Hashtable)(Hashtable)domainTb.get(domain);
            if (canonical_key_property_list_string.length() == 0) {
                result.addAll(moiTb.values());
            } else {
                if (on_pattern == null) on_pattern = new RepositorySupport$ObjectNamePattern(name);
                addAllMatching(moiTb, result, on_pattern);
            }
            return result;
        }
        synchronized (domainTb) {
            char[] dom2Match = name.getDomain().toCharArray();
            String nextDomain;
            char[] theDom;
            for (final Enumeration enumi = domainTb.keys(); enumi.hasMoreElements(); ) {
                nextDomain = (String)(String)enumi.nextElement();
                theDom = nextDomain.toCharArray();
                if (wildmatch(theDom, dom2Match, 0, 0)) {
                    final Hashtable moiTb = (Hashtable)(Hashtable)domainTb.get(nextDomain);
                    if (canonical_key_property_list_string.length() == 0) result.addAll(moiTb.values()); else {
                        if (on_pattern == null) on_pattern = new RepositorySupport$ObjectNamePattern(name);
                        addAllMatching(moiTb, result, on_pattern);
                    }
                }
            }
        }
        return result;
    }
    
    public void remove(final ObjectName name) throws InstanceNotFoundException {
        if (isTraceOn()) {
            trace("remove", "name=" + name);
        }
        String dom = name.getDomain().intern();
        if (dom.length() == 0) dom = domain;
        Object tmp_object = domainTb.get(dom);
        if (tmp_object == null) {
            throw new InstanceNotFoundException(name.toString());
        }
        Hashtable moiTb = (Hashtable)(Hashtable)tmp_object;
        if (moiTb.remove(name.getCanonicalKeyPropertyListString()) == null) {
            throw new InstanceNotFoundException(name.toString());
        }
        nbElements--;
        if (moiTb.isEmpty()) {
            domainTb.remove(dom);
            if (dom == domain) domainTb.put(domain, new Hashtable());
        }
    }
    
    public Integer getCount() {
        return new Integer(nbElements);
    }
    
    public String getDefaultDomain() {
        return domain;
    }
}
