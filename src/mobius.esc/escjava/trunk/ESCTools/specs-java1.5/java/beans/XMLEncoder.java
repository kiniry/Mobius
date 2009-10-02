package java.beans;

import java.io.*;
import java.util.*;
import java.lang.reflect.*;

public class XMLEncoder extends Encoder {
    {
    }
    private static String encoding = "UTF-8";
    private OutputStream out;
    private Object owner;
    private int indentation = 0;
    private boolean internal = false;
    private Map valueToExpression;
    private Map targetToStatementList;
    private boolean preambleWritten = false;
    private NameGenerator nameGenerator;
    {
    }
    
    public XMLEncoder(OutputStream out) {
        
        this.out = out;
        valueToExpression = new IdentityHashMap();
        targetToStatementList = new IdentityHashMap();
        nameGenerator = new NameGenerator();
    }
    
    public void setOwner(Object owner) {
        this.owner = owner;
        writeExpression(new Expression(this, "getOwner", new Object[0]));
    }
    
    public Object getOwner() {
        return owner;
    }
    
    public void writeObject(Object o) {
        if (internal) {
            super.writeObject(o);
        } else {
            writeStatement(new Statement(this, "writeObject", new Object[]{o}));
        }
    }
    
    private Vector statementList(Object target) {
        Vector list = (Vector)(Vector)targetToStatementList.get(target);
        if (list != null) {
            return list;
        }
        list = new Vector();
        targetToStatementList.put(target, list);
        return list;
    }
    
    private void mark(Object o, boolean isArgument) {
        if (o == null || o == this) {
            return;
        }
        XMLEncoder$ValueData d = getValueData(o);
        Expression exp = d.exp;
        if (o.getClass() == String.class && exp == null) {
            return;
        }
        if (isArgument) {
            d.refs++;
        }
        if (d.marked) {
            return;
        }
        d.marked = true;
        Object target = exp.getTarget();
        if (!(target instanceof Class)) {
            statementList(target).add(exp);
            d.refs++;
        }
        mark(exp);
    }
    
    private void mark(Statement stm) {
        Object[] args = stm.getArguments();
        for (int i = 0; i < args.length; i++) {
            Object arg = args[i];
            mark(arg, true);
        }
        mark(stm.getTarget(), false);
    }
    
    public void writeStatement(Statement oldStm) {
        boolean internal = this.internal;
        this.internal = true;
        try {
            super.writeStatement(oldStm);
            mark(oldStm);
            statementList(oldStm.getTarget()).add(oldStm);
        } catch (Exception e) {
            getExceptionListener().exceptionThrown(new Exception("XMLEncoder: discarding statement " + oldStm, e));
        }
        this.internal = internal;
    }
    
    public void writeExpression(Expression oldExp) {
        boolean internal = this.internal;
        this.internal = true;
        Object oldValue = getValue(oldExp);
        if (get(oldValue) == null || (oldValue instanceof String && !internal)) {
            getValueData(oldValue).exp = oldExp;
            super.writeExpression(oldExp);
        }
        this.internal = internal;
    }
    
    public void flush() {
        if (!preambleWritten) {
            writeln("<?xml version=" + quote("1.0") + " encoding=" + quote(encoding) + "?>");
            writeln("<java version=" + quote(System.getProperty("java.version")) + " class=" + quote(XMLDecoder.class.getName()) + ">");
            preambleWritten = true;
        }
        indentation++;
        Vector roots = statementList(this);
        for (int i = 0; i < roots.size(); i++) {
            Statement s = (Statement)(Statement)roots.get(i);
            if ("writeObject".equals(s.getMethodName())) {
                outputValue(s.getArguments()[0], this, true);
            } else {
                outputStatement(s, this, false);
            }
        }
        indentation--;
        try {
            out.flush();
        } catch (IOException e) {
            getExceptionListener().exceptionThrown(e);
        }
        clear();
    }
    
    void clear() {
        super.clear();
        nameGenerator.clear();
        valueToExpression.clear();
        targetToStatementList.clear();
    }
    
    public void close() {
        flush();
        writeln("</java>");
        try {
            out.close();
        } catch (IOException e) {
            getExceptionListener().exceptionThrown(e);
        }
    }
    
    private String quote(String s) {
        return "\"" + s + "\"";
    }
    
    private XMLEncoder$ValueData getValueData(Object o) {
        XMLEncoder$ValueData d = (XMLEncoder$ValueData)(XMLEncoder$ValueData)valueToExpression.get(o);
        if (d == null) {
            d = new XMLEncoder$ValueData(this, null);
            valueToExpression.put(o, d);
        }
        return d;
    }
    
    private static String quoteCharacters(String s) {
        StringBuffer result = null;
        for (int i = 0, max = s.length(), delta = 0; i < max; i++) {
            char c = s.charAt(i);
            String replacement = null;
            if (c == '&') {
                replacement = "&amp;";
            } else if (c == '<') {
                replacement = "&lt;";
            } else if (c == '\r') {
                replacement = "&#13;";
            } else if (c == '>') {
                replacement = "&gt;";
            } else if (c == '\"') {
                replacement = "&quot;";
            } else if (c == '\'') {
                replacement = "&apos;";
            }
            if (replacement != null) {
                if (result == null) {
                    result = new StringBuffer(s);
                }
                result.replace(i + delta, i + delta + 1, replacement);
                delta += (replacement.length() - 1);
            }
        }
        if (result == null) {
            return s;
        }
        return result.toString();
    }
    
    private void writeln(String exp) {
        try {
            for (int i = 0; i < indentation; i++) {
                out.write(' ');
            }
            out.write(exp.getBytes(encoding));
            out.write(" \n".getBytes(encoding));
        } catch (IOException e) {
            getExceptionListener().exceptionThrown(e);
        }
    }
    
    private void outputValue(Object value, Object outer, boolean isArgument) {
        if (value == null) {
            writeln("<null/>");
            return;
        }
        if (value instanceof Class) {
            writeln("<class>" + ((Class)(Class)value).getName() + "</class>");
            return;
        }
        XMLEncoder$ValueData d = getValueData(value);
        if (d.exp != null) {
            Object target = d.exp.getTarget();
            String methodName = d.exp.getMethodName();
            if (target == null || methodName == null) {
                throw new NullPointerException((target == null ? "target" : "methodName") + " should not be null");
            }
            if (target instanceof Field && methodName.equals("get")) {
                Field f = (Field)(Field)target;
                writeln("<object class=" + quote(f.getDeclaringClass().getName()) + " field=" + quote(f.getName()) + "/>");
                return;
            }
            Class primitiveType = ReflectionUtils.primitiveTypeFor(value.getClass());
            if (primitiveType != null && target == value.getClass() && methodName.equals("new")) {
                String primitiveTypeName = primitiveType.getName();
                if (primitiveType == Character.TYPE) {
                    value = quoteCharacters(((Character)(Character)value).toString());
                }
                writeln("<" + primitiveTypeName + ">" + value + "</" + primitiveTypeName + ">");
                return;
            }
        } else if (value instanceof String) {
            writeln("<string>" + quoteCharacters((String)(String)value) + "</string>");
            return;
        }
        if (d.name != null) {
            writeln("<object idref=" + quote(d.name) + "/>");
            return;
        }
        outputStatement(d.exp, outer, isArgument);
    }
    
    private void outputStatement(Statement exp, Object outer, boolean isArgument) {
        Object target = exp.getTarget();
        String methodName = exp.getMethodName();
        if (target == null || methodName == null) {
            throw new NullPointerException((target == null ? "target" : "methodName") + " should not be null");
        }
        Object[] args = exp.getArguments();
        boolean expression = exp.getClass() == Expression.class;
        Object value = (expression) ? getValue((Expression)(Expression)exp) : null;
        String tag = (expression && isArgument) ? "object" : "void";
        String attributes = "";
        XMLEncoder$ValueData d = getValueData(value);
        if (expression) {
            if (d.refs > 1) {
                String instanceName = nameGenerator.instanceName(value);
                d.name = instanceName;
                attributes = attributes + " id=" + quote(instanceName);
            }
        }
        if (target == outer) {
        } else if (target == Array.class && methodName.equals("newInstance")) {
            tag = "array";
            attributes = attributes + " class=" + quote(((Class)(Class)args[0]).getName());
            attributes = attributes + " length=" + quote(args[1].toString());
            args = new Object[]{};
        } else if (target.getClass() == Class.class) {
            attributes = attributes + " class=" + quote(((Class)(Class)target).getName());
        } else {
            d.refs = 2;
            outputValue(target, outer, false);
            outputValue(value, outer, false);
            return;
        }
        if ((!expression && methodName.equals("set") && args.length == 2 && args[0] instanceof Integer) || (expression && methodName.equals("get") && args.length == 1 && args[0] instanceof Integer)) {
            attributes = attributes + " index=" + quote(args[0].toString());
            args = (args.length == 1) ? new Object[]{} : new Object[]{args[1]};
        } else if ((!expression && methodName.startsWith("set") && args.length == 1) || (expression && methodName.startsWith("get") && args.length == 0)) {
            attributes = attributes + " property=" + quote(Introspector.decapitalize(methodName.substring(3)));
        } else if (!methodName.equals("new") && !methodName.equals("newInstance")) {
            attributes = attributes + " method=" + quote(methodName);
        }
        Vector statements = statementList(value);
        if (args.length == 0 && statements.size() == 0) {
            writeln("<" + tag + attributes + "/>");
            return;
        }
        writeln("<" + tag + attributes + ">");
        indentation++;
        for (int i = 0; i < args.length; i++) {
            outputValue(args[i], null, true);
        }
        for (int i = 0; i < statements.size(); i++) {
            Statement s = (Statement)(Statement)statements.get(i);
            outputStatement(s, value, false);
        }
        indentation--;
        writeln("</" + tag + ">");
    }
}
