package mobius.cct.repositories.classfile;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import mobius.cct.repositories.classfile.types.FieldType;
import mobius.cct.repositories.classfile.types.ResultType;
import mobius.cct.util.ArrayIterator;

/**
 * Method name with types of arguments and result.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class MethodName {
  /**
   * Types of arguments.
   */
  private final FieldType[] fArgs;
  
  /**
   * Type of result.
   */
  private final ResultType fResult;
  
  /**
   * Name.
   */
  private final String fName;
  
  /**
   * Constructor.
   * @param name Method name.
   * @param args Argument types.
   * @param result Result type.
   */
  public MethodName(final String name, 
                    final FieldType[] args, 
                    final ResultType result) {
    fName = name;
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
   * Decode method name and type in internal form.
   * @param reader Input stream.
   * @return Parsed method.
   * @throws IOException .
   */
  public static MethodName parse(final Reader reader)
    throws IOException {
    
    final BufferedReader r = new BufferedReader(reader);
    
    final StringBuilder name = new StringBuilder();
    
    r.mark(1);
    int c = r.read();
    while ((c != -1) && (c != '(')) {
      name.append((char)c);
      r.mark(1);
      c = r.read();
    }
    if (c != '(') {
      throw new java.io.EOFException();
    }
    r.reset();
    final FieldType[] args = parseArgs(r);
    
    final ResultType result = ResultType.parse(r);
    return new MethodName(name.toString(), args, result);
  }
  
  /**
   * Decode method name and type in internal form.
   * @param m Encoded method.
   * @return Parsed method.
   * @throws IOException .
   */
  public static MethodName parse(final String m) throws IOException {
    return parse(new StringReader(m)); 
  }
  
  /**
   * Create method with given name and encoded type. If the type
   * is invalid, null is returned.
   * @param name Method name.
   * @param type Encoded type (like "(IIB)V").
   * @return MethodName instance.
   */
  public static MethodName get(final String name, final String type) {
    try {
      final StringReader reader = new StringReader(type);
      final FieldType[] args = parseArgs(reader);
      final ResultType result = ResultType.parse(reader);
      return new MethodName(name, args, result);
    } catch (IOException e) {
      return null;
    }
  }
  
  /**
   * Get types of arguments.
   * @return Iterator.
   */
  public Iterator<FieldType> argumentTypes() {
    return new ArrayIterator<FieldType>(fArgs);
  }
  
  /**
   * Get result type. 
   * @return Result type.
   */
  public ResultType resultType() {
    return fResult;
  }
  
  /**
   * Get method name.
   * @return Name.
   */
  public String getName() {
    return fName;
  }
  
  /**
   * Encode method name and type in internal form.
   * @return Encoded method name and type.
   */
  public String internalForm() {
    final StringBuilder sb = new StringBuilder();
    sb.append(fName);
    sb.append('(');
    for (int i = 0; i < fArgs.length; i++) {
      sb.append(fArgs[i].internalForm());
    }
    sb.append(')');
    if (fResult == null) {
      sb.append('V');
    } else {
      sb.append(fResult.internalForm());
    }
    return sb.toString();
  }
  
  /**
   * Encode method name and type in external form.
   * @return Encoded method name and type.
   */
  public String externalForm() {
    final StringBuilder sb = new StringBuilder();
    
    sb.append(fResult.externalForm());
    sb.append(' ');
    sb.append(fName);
    sb.append('(');
    for (int i = 0; i < fArgs.length; i++) {
      sb.append(fArgs[i].externalForm());
      if (i < fArgs.length - 1) {
        sb.append(", ");
      }
    }
    sb.append(')');
    return sb.toString();
  }
  
}
