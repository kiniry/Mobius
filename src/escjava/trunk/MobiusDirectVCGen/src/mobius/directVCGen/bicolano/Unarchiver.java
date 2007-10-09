package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * A class to inflat bicolano as well as the static preludes from
 * a jar file.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Unarchiver {
  /** size of the read buffer. */
  private static final int BUFF_SIZE = 1024;
  /** the directory in the archive of bicolano: /Formalisation/Bicolano. */
  private static final String bicodir = "Formalisation" + File.separator + "Bicolano";
  /** the directory in the archive of the library: /Formalisation/Library. */
  private static final String libdir = "Formalisation" + File.separator + "Library";
  /** the directory in the archive of the Map library: /Formalisation/Library/Map. */
  private static final String libmapdir = libdir + File.separator + "Map";
  
  
  private static final String liblogicdir = "Formalisation" + File.separator + "Logic";

  /** the jar file containing bicolano. */
  private final File fBicoFile;

  /**
   * Create an object to unarchive the specified 
   * file containing bicolano and the prelude.
   * @param file a jar file containing bicolano
   * @throws IOException if the file cannot be read
   */
  public Unarchiver(final File file) throws IOException {
    this.fBicoFile = file;
    System.out.println("Bicolano file's path is: " + file);
    if (!file.canRead()) {
      throw new IOException("Bad path given to find Bicolano, exiting... ");

    }
  }

  /**
   * Copy all the data contained in the input to the output.
   * @param in The input stream
   * @param out The output stream
   * @throws IOException If an error of reading or writing occur.
   */
  public static void copy(final InputStream in, 
                          final FileOutputStream out) throws IOException {
    final byte [] buff = new byte[BUFF_SIZE];
    int res;
    while ((res = in.read(buff)) > 0) {
      out.write(buff, 0, res);
    }
  }

  /**
   * Inflat the content of the bicolano jar file to a specific directory.
   * @param basedir The directory where to inflat bicolano
   * @throws IOException if an error of reading or writing occur.
   */
  public void inflat(final File basedir) throws IOException {
    final File b = new File(basedir, "Formalisation");
    if (!b.exists()) {
      System.out.println("Bicolano seems not present in the basedir, inflating it.");
    }

    final JarFile bico = new JarFile(fBicoFile);
    final EntryIterator iter = new EntryIterator(bico.entries());

    for (JarEntry entry: iter) {
      final String name = entry.getName(); 
      if (name.startsWith("META-INF")) { // we skip meta-inf
        continue;
      }

      if (name.startsWith("Formalisation")) {
        // making missing directory
        final File f = new File(basedir, entry.getName());
        f.getParentFile().mkdirs();

      }
      if (name.startsWith("defs_types")) {
        // special case for prelude file
        inflatPrelude(basedir, bico, entry);
        continue;
      }
      else {
        final File f = new File(basedir, entry.getName());
        final FileOutputStream out = (new FileOutputStream(f));
        final InputStream in = bico.getInputStream(entry);
        copy(in, out);
        out.close();
        in.close();
      }
    }
  }

  /**
   * Inflat the prelude which has been found in the JarFile.
   * @param basedir the directory where everything is inflated
   * @param bico the jar file containing bicolano
   * @param entry the current entry of the prelude file
   * @throws IOException in case of a missing file or writing error
   */
  private void inflatPrelude(final File basedir, final JarFile bico, 
                             final JarEntry entry) throws IOException {
    final File f = new File(basedir, entry.getName());
    final PrintStream out = new PrintStream(new FileOutputStream(f));
    final LineNumberReader in = new LineNumberReader(new InputStreamReader(
                                           bico.getInputStream(entry)));
    // we skip the first three lines
    in.readLine(); in.readLine(); in.readLine(); in.readLine();
    // and we replace them by system dependent lines
    out.println("Add LoadPath \"" + //basedir.getAbsolutePath() + 
                //File.separator + 
                bicodir + "\".");
    out.println("Add LoadPath \"" + // basedir.getAbsolutePath() + 
                //File.separator + 
                libdir + "\".");
    out.println("Add LoadPath \"" + //basedir.getAbsolutePath() + 
                //File.separator + 
                libmapdir + "\".");
    out.println("Add LoadPath \"" + //basedir.getAbsolutePath() + 
                //File.separator + 
                liblogicdir + "\".");
    String str;
    while ((str = in.readLine()) != null) {
      out.println(str);
    }
    out.close();
    in.close();
  }

  /**
   * An object to make Iterable an enumeration of a jar.
   * Just for convenience... 
   * I don't understand why it is not already available in Java's jar
   * library. Anyone got a clue? If I am somewhat wrong please mail me
   * I'd be glad to know how I could handle that more elegantly.
   * @author J. Charles
   */
  private static class EntryIterator implements Iterator<JarEntry>, Iterable<JarEntry> {
    /** the enumeration to make iterable. */
    private Enumeration<JarEntry> fEnum;

    /**
     * Create an iterable object from an enumeration object.
     * @param enu the enumeration to turn to iterable.
     */
    public EntryIterator(final Enumeration<JarEntry>  enu) {
      this.fEnum = enu;
    }

    /**
     * @return tells if there is an available element in the iterator
     */
    public boolean hasNext() {
      return fEnum.hasMoreElements();
    }

    /**
     * @return returns the next element of the iterator
     */
    public JarEntry next() {
      return fEnum.nextElement();
    }

    /**
     * Unsupported op.
     */
    public void remove() {
      throw new UnsupportedOperationException();

    }

    /**
     * @return an iterator on the entries
     */
    public Iterator<JarEntry> iterator() {
      return this;
    }
  }
}
