package mobius.cct.constantpool.readers;

import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;

import mobius.cct.constantpool.UnknownConstantException;
import mobius.cct.constantpool.entries.ClassEntry;
import mobius.cct.constantpool.entries.DoubleEntry;
import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.entries.FieldrefEntry;
import mobius.cct.constantpool.entries.FloatEntry;
import mobius.cct.constantpool.entries.IntegerEntry;
import mobius.cct.constantpool.entries.InterfaceMethodrefEntry;
import mobius.cct.constantpool.entries.LongEntry;
import mobius.cct.constantpool.entries.MethodrefEntry;
import mobius.cct.constantpool.entries.NameAndTypeEntry;
import mobius.cct.constantpool.entries.StringEntry;
import mobius.cct.constantpool.entries.Utf8Entry;

/**
 * EntryReader capable of reading all constants
 * defined in JSR-202.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultEntryReader implements EntryReader {

  //TODO: Use a dictionary of readers instead of case.
  //CHECKSTYLE:OFF
  /**
   * Read entry.
   * @param is Input stream.
   * @param t Constant type.
   * @return Entry.
   * @throws UnknownConstantException If constants of type t are
   * not supported.
   * @throws IOException .
   */
  public Entry read(final InputStream is, 
                    final int t) throws IOException,
  UnknownConstantException {
    final DataInputStream ds = new DataInputStream(is);
    switch (t) {
      case Entry.CONSTANT_Class: {
        final int name = ds.readShort();
        return new ClassEntry(name);
      }
      case Entry.CONSTANT_Fieldref: {
        final int className = ds.readShort();
        final int sig = ds.readShort();
        return new FieldrefEntry(className, sig);
      }            
      case Entry.CONSTANT_Methodref: {
        final int className = ds.readShort();
        final int sig = ds.readShort();
        return new MethodrefEntry(className, sig);
      }         
      case Entry.CONSTANT_InterfaceMethodref: {
        final int className = ds.readShort();
        final int sig = ds.readShort();
        return new InterfaceMethodrefEntry(className, sig);
      }
      case Entry.CONSTANT_String: {
        final int valueIndex = ds.readShort();
        return new StringEntry(valueIndex);
      }           
      case Entry.CONSTANT_Integer: {
        final int value = ds.readInt();
        return new IntegerEntry(value);
      }          
      case Entry.CONSTANT_Float: {
        final float value = ds.readFloat();
        return new FloatEntry(value);
      }           
      case Entry.CONSTANT_Long: {
        final long value = ds.readLong();
        return new LongEntry(value);
      }           
      case Entry.CONSTANT_Double: {
        final double value = ds.readDouble();
        return new DoubleEntry(value);
      }            
      case Entry.CONSTANT_NameAndType: {
        final int name = ds.readShort();
        final int type = ds.readShort();
        return new NameAndTypeEntry(name, type);
      }      
      case Entry.CONSTANT_Utf8: {
        final String value = ds.readUTF();
        return new Utf8Entry(value);
      }
      default:
        throw new UnknownConstantException(t);
      }
  }
  //CHECKSTYLE:OFF
}
