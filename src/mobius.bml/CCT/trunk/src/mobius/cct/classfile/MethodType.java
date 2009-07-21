package mobius.cct.classfile;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import mobius.cct.classfile.types.FieldType;
import mobius.cct.classfile.types.ResultType;
import mobius.cct.util.ArrayIterator;

/**
 * Type of a method.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class MethodType implements Comparable<MethodType> {
  /**
   * Types of arguments.
   */
  private final FieldType[] fArgs;
  
  /**
   * Type of result.
   */
  private final ResultType fResult;
  
  /**
   * Constructor.
   * @param args Argument types.
   * @param result Result type.
   */
  public MethodType(final FieldType[] args, 
                    final ResultType result) {
    fResult = result;
    fArgs = new FieldType[args.length];
    for (int i = 0; i < args.length; i++) {
      fArgs[i] = args[i];
    }
  }
  
  /**
   * Read argument list in internal form.
   * @param reader Argument list. This reader must support mark().
   * @return Array of argument types.
   * @throws IOException .
   */
  private static FieldType[] parseArgs(final Reader reader) 
    throws IOException {
    
    final List<FieldType> args = new ArrayList<FieldType>();
    
    if (reader.read() != '(') {
      throw new IOException("?");
    }
    reader.mark(1);
    int c = reader.read();
    while ((c != -1) && (c != ')')) {
      reader.reset();
      args.add(FieldType.parse(reader));
      reader.mark(1);
      c = reader.read();
    }
    if (c != ')') {
      throw new java.io.EOFException();
    }
    return args.toArray(new FieldType[]{});
  }
  
  /**
   * Read argument list in internal form.
   * @param args Argument list.
   * @return Array of argument types.
   * @throws IOException .
   */
  public static FieldType[] parseArgs(final String args) 
    throws IOException {
    return parseArgs(new StringReader(args));
  }
  
  /**
   * Decode method type in internal form.
   * @param reader Input stream.
   * @return Parsed method.
   * @throws IOException .
   */
  public static MethodType parse(final Reader reader)
    throws IOException {
    
    final BufferedReader r = new BufferedReader(reader);
    
    final FieldType[] args = parseArgs(r);
    final ResultType result = ResultType.parse(r);
    return new MethodType(args, result);
  }

  /**
   * Decode method type in internal form.
   * @param m Encoded method.
   * @return Parsed method.
   * @throws IOException .
   */
  public static MethodType parse(final String m) throws IOException {
    return parse(new StringReader(m)); 
  }
  
  /**
   * Get argument type.
   * @return Iterator.
   */
  public Iterator<FieldType> getArgs() {
    return new ArrayIterator<FieldType>(fArgs);
  }
  
  /**
   * Get return type.
   * @return Return type.
   */
  public ResultType getResult() {
    return fResult;
  }
  
  /**
   * Encode method type in internal form.
   * @return Encoded method name and type.
   */
  public String internalForm() {
    final StringBuilder sb = new StringBuilder();
    sb.append('(');
    for (int i = 0; i < fArgs.length; i++) {
      sb.append(fArgs[i].internalForm());
    }
    sb.append(')');
    sb.append(fResult.internalForm());
    return sb.toString();
  }
  
  /**
   * Hashcode.
   * @return hashcode.
   */
  @Override
  public int hashCode() {
    return internalForm().hashCode();
  }
  
  /**
   * Compare method types.
   * @param t Method type.
   * @return .
   */
  public int compareTo(final MethodType t) {
    return internalForm().compareTo(t.internalForm());
  }
  
  /**
   * Equals.
   * @param obj Object to compare.
   * @return .
   */
  @Override
  public boolean equals(final Object obj) {
    if (obj == null) {
      return false;
    }
    if (obj.getClass().equals(this.getClass())) {
      return compareTo((MethodType)obj) == 0;
    } else {
      return obj.equals(this);
    }
  }
    
}
