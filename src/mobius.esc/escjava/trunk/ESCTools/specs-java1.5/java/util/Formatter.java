package java.util;

import java.io.BufferedWriter;
import java.io.Closeable;
import java.io.IOException;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileNotFoundException;
import java.io.Flushable;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.UnsupportedEncodingException;
import java.text.DecimalFormatSymbols;
import java.util.Locale;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class Formatter implements Closeable, Flushable {
    
    /*synthetic*/ static char access$300(Formatter x0) {
        return x0.zero;
    }
    
    /*synthetic*/ static double access$202(double x0) {
        return scaleUp = x0;
    }
    
    /*synthetic*/ static double access$200() {
        return scaleUp;
    }
    
    /*synthetic*/ static Appendable access$000(Formatter x0) {
        return x0.a;
    }
    private Appendable a;
    private Locale l;
    private IOException lastException;
    private char zero = '0';
    private static double scaleUp;
    private static final int MAX_FD_CHARS = 30;
    
    private void init(Appendable a, Locale l) {
        this.a = a;
        this.l = l;
        setZero();
    }
    
    public Formatter() {
        
        init(new StringBuilder(), Locale.getDefault());
    }
    
    public Formatter(Appendable a) {
        
        init(a, Locale.getDefault());
    }
    
    public Formatter(Locale l) {
        
        init(new StringBuilder(), l);
    }
    
    public Formatter(Appendable a, Locale l) {
        
        if (a == null) a = new StringBuilder();
        init(a, l);
    }
    
    public Formatter(String fileName) throws FileNotFoundException {
        
        init(new BufferedWriter(new OutputStreamWriter(new FileOutputStream(fileName))), Locale.getDefault());
    }
    
    public Formatter(String fileName, String csn) throws FileNotFoundException, UnsupportedEncodingException {
        this(fileName, csn, Locale.getDefault());
    }
    
    public Formatter(String fileName, String csn, Locale l) throws FileNotFoundException, UnsupportedEncodingException {
        
        init(new BufferedWriter(new OutputStreamWriter(new FileOutputStream(fileName), csn)), l);
    }
    
    public Formatter(File file) throws FileNotFoundException {
        
        init(new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file))), Locale.getDefault());
    }
    
    public Formatter(File file, String csn) throws FileNotFoundException, UnsupportedEncodingException {
        this(file, csn, Locale.getDefault());
    }
    
    public Formatter(File file, String csn, Locale l) throws FileNotFoundException, UnsupportedEncodingException {
        
        init(new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file), csn)), l);
    }
    
    public Formatter(PrintStream ps) {
        
        if (ps == null) throw new NullPointerException();
        init((Appendable)ps, Locale.getDefault());
    }
    
    public Formatter(OutputStream os) {
        
        init(new BufferedWriter(new OutputStreamWriter(os)), Locale.getDefault());
    }
    
    public Formatter(OutputStream os, String csn) throws UnsupportedEncodingException {
        this(os, csn, Locale.getDefault());
    }
    
    public Formatter(OutputStream os, String csn, Locale l) throws UnsupportedEncodingException {
        
        init(new BufferedWriter(new OutputStreamWriter(os, csn)), l);
    }
    
    private void setZero() {
        if ((l != null) && !l.equals(Locale.US)) {
            DecimalFormatSymbols dfs = new DecimalFormatSymbols(l);
            zero = dfs.getZeroDigit();
        }
    }
    
    public Locale locale() {
        ensureOpen();
        return l;
    }
    
    public Appendable out() {
        ensureOpen();
        return a;
    }
    
    public String toString() {
        ensureOpen();
        return a.toString();
    }
    
    public void flush() {
        ensureOpen();
        if (a instanceof Flushable) {
            try {
                ((Flushable)(Flushable)a).flush();
            } catch (IOException ioe) {
                lastException = ioe;
            }
        }
    }
    
    public void close() {
        if (a == null) return;
        try {
            if (a instanceof Closeable) ((Closeable)(Closeable)a).close();
        } catch (IOException ioe) {
            lastException = ioe;
        } finally {
            a = null;
        }
    }
    
    private void ensureOpen() {
        if (a == null) throw new FormatterClosedException();
    }
    
    public IOException ioException() {
        return lastException;
    }
    
    public Formatter format(String format, Object [] args) {
        return format(l, format, args);
    }
    
    public Formatter format(Locale l, String format, Object [] args) {
        ensureOpen();
        int last = -1;
        int lasto = -1;
        Formatter$FormatString[] fsa = parse(format);
        for (int i = 0; i < fsa.length; i++) {
            Formatter$FormatString fs = fsa[i];
            int index = fs.index();
            try {
                switch (index) {
                case -2: 
                    fs.print(null, l);
                    break;
                
                case -1: 
                    if (last < 0 || (args != null && last > args.length - 1)) throw new MissingFormatArgumentException(fs.toString());
                    fs.print((args == null ? null : args[last]), l);
                    break;
                
                case 0: 
                    lasto++;
                    last = lasto;
                    if (args != null && lasto > args.length - 1) throw new MissingFormatArgumentException(fs.toString());
                    fs.print((args == null ? null : args[lasto]), l);
                    break;
                
                default: 
                    last = index - 1;
                    if (args != null && last > args.length - 1) throw new MissingFormatArgumentException(fs.toString());
                    fs.print((args == null ? null : args[last]), l);
                    break;
                
                }
            } catch (IOException x) {
                lastException = x;
            }
        }
        return this;
    }
    private static final String formatSpecifier = "%(\\d+\\$)?([-#+ 0,(\\<]*)?(\\d+)?(\\.\\d+)?([tT])?([a-zA-Z%])";
    private static Pattern fsPattern = Pattern.compile(formatSpecifier);
    
    private Formatter$FormatString[] parse(String s) {
        ArrayList al = new ArrayList();
        Matcher m = fsPattern.matcher(s);
        int i = 0;
        while (i < s.length()) {
            if (m.find(i)) {
                if (m.start() != i) {
                    checkText(s.substring(i, m.start()));
                    al.add(new Formatter$FixedString(this, s.substring(i, m.start())));
                }
                String[] sa = new String[6];
                for (int j = 0; j < m.groupCount(); j++) {
                    sa[j] = m.group(j + 1);
                }
                al.add(new Formatter$FormatSpecifier(this, this, sa));
                i = m.end();
            } else {
                checkText(s.substring(i));
                al.add(new Formatter$FixedString(this, s.substring(i)));
                break;
            }
        }
        return (Formatter$FormatString[])(Formatter$FormatString[])al.toArray(new Formatter$FormatString[0]);
    }
    
    private void checkText(String s) {
        int idx;
        if ((idx = s.indexOf('%')) != -1) {
            char c = (idx > s.length() - 2 ? '%' : s.charAt(idx + 1));
            throw new UnknownFormatConversionException(String.valueOf(c));
        }
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
