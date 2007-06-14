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
	/** the directory in the archive of bicolano: /Formalisation/Bicolano */
	private static final String bicodir = "Formalisation" + File.separator + "Bicolano";
	/** the directory in the archive of the library: /Formalisation/Library */
	private static final String libdir = "Formalisation" + File.separator + "Library";
	/** the directory in the archive of the Map library: /Formalisation/Library/Map */
	private static final String libmapdir = libdir + File.separator + "Map";

	/** the jar file containing bicolano */
	private final File bicofile;
	
	/**
	 * Create an object to unarchive the specified 
	 * file containing bicolano and the prelude.
	 * @param file a jar file containing bicolano
	 * @throws IOException if the file cannot be read
	 */
	public Unarchiver(File file) throws IOException {
		this.bicofile = file;
		System.out.println("Bicolano file's path is: " + file);
		if(!file.canRead()) {
			throw new IOException("Bad path given to find Bicolano, exiting... ");
			
		}
	}

	/**
	 * Copy all the data contained in the input to the output.
	 * @param in The input stream
	 * @param out The output stream
	 * @throws IOException If an error of reading or writing occur.
	 */
	public static void copy(InputStream in, FileOutputStream out) throws IOException {
		final byte [] buff = new byte[1024];
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
	public void inflat(File basedir) throws IOException {
		File b = new File(basedir, "Formalisation");
		if(!b.exists()) {
			System.out.println("Bicolano seems not present in the basedir, inflating it.");
		}

		JarFile bico = new JarFile(bicofile);
		EntryIterator iter = new EntryIterator(bico.entries());

		for (JarEntry entry: iter) {
			String name =entry.getName(); 
			if(name.startsWith("META-INF"))
				continue;
			
			File f = new File(basedir, entry.getName());
			if(name.startsWith("Formalisation")) {
				f.getParentFile().mkdirs();
				
			}
			if(name.startsWith("defs_")) {
				// special case for prelude file
				PrintStream out = new PrintStream(new FileOutputStream(f));
				LineNumberReader in = new LineNumberReader(new InputStreamReader(bico.getInputStream(entry)));
				// we skip the first three lines
				in.readLine(); in.readLine(); in.readLine();
				// and we replace them by system dependent lines
				out.println("Add LoadPath \"" + basedir.getAbsolutePath() + File.separator + bicodir + "\".");
				out.println("Add LoadPath \"" + basedir.getAbsolutePath() + File.separator + libdir + "\".");
				out.println("Add LoadPath \"" + basedir.getAbsolutePath() + File.separator + libmapdir + "\".");
				String str;
				while((str = in.readLine()) != null) {
					out.println(str);
				}
				out.close();
				in.close();
				continue;
			}
			FileOutputStream out = (new FileOutputStream(f));
			InputStream in = bico.getInputStream(entry);
			copy(in, out);
			out.close();
			in.close();
		}
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
		/** the enumeration to make iterable */
		private Enumeration<JarEntry> e;
		
		/**
		 * Create an iterable object from an enumeration object.
		 * @param e the enumeration to turn to iterable.
		 */
		public EntryIterator(Enumeration<JarEntry>  e) {
			this.e = e;
		}

		/*
		 * (non-Javadoc)
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			return e.hasMoreElements();
		}

		/*
		 * (non-Javadoc)
		 * @see java.util.Iterator#next()
		 */
		public JarEntry next() {
			return e.nextElement();
		}

		/*
		 * (non-Javadoc)
		 * @see java.util.Iterator#remove()
		 */
		public void remove() {
			throw new UnsupportedOperationException();
			
		}

		/*
		 * (non-Javadoc)
		 * @see java.lang.Iterable#iterator()
		 */
		public Iterator<JarEntry> iterator() {
			return this;
		}
  }
}
