package mobius.cct.constantpool.readers;

import java.io.IOException;
import java.io.InputStream;

import mobius.cct.constantpool.UnknownConstantException;
import mobius.cct.constantpool.entries.Entry;

/**
 * Interface of objects used to read constant pool
 * entries from class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface EntryReader {
  /**
   * Read and return single entry from
   * given input stream. Entry type
   * is not in the stream.
   * @param is Input stream.
   * @param t Entry type.
   * @return Entry.
   * @throws UnknownConstantException If a constant of unsupported
   * type is encountered.
   * @throws IOException .
   */
  Entry read(InputStream is, int t) 
    throws IOException, UnknownConstantException;
}
