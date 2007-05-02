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

public class Unarchiver {
	private final File bicofile;
	private static final String bicodir = "Formalisation" + File.separator + "Bicolano";
	private static final String libdir = "Formalisation" + File.separator + "Library";
	private static final String libmapdir = libdir + File.separator + "Map";
	public Unarchiver(File bicodir) {
		this.bicofile = bicodir;
		System.out.println("Bicolano file's path is: " + bicodir);
		if(!bicodir.canRead()) {
			System.out.println("Bad path given to find Bicolano, exiting... ");
			return;
		}
	}
	public static void copy(InputStream in, FileOutputStream out) throws IOException {
		final byte [] buff = new byte[1024];
		int res;
		while ((res = in.read(buff)) > 0) {
			out.write(buff, 0, res);
		}
	}
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
	
	private static class EntryIterator implements Iterator<JarEntry>, Iterable<JarEntry> {
		Enumeration<JarEntry> e;
		public EntryIterator(Enumeration<JarEntry>  e) {
			this.e = e;
		}

		public boolean hasNext() {
			return e.hasMoreElements();
		}

		public JarEntry next() {
			return e.nextElement();
		}

		public void remove() {
			throw new UnsupportedOperationException();
			
		}

		public Iterator<JarEntry> iterator() {
			return this;
		}
		
	};
}
