package mobius.directVCGen.bicolano;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

public class Unarchiver {
	private final File bicodir;

	public Unarchiver(File bicodir) {
		this.bicodir = bicodir;
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

		JarFile bico = new JarFile(bicodir);
		EntryIterator iter = new EntryIterator(bico.entries());

		for (JarEntry entry: iter) {
			String name =entry.getName(); 
			if(name.startsWith("META-INF"))
				continue;
			
			File f = new File(basedir, entry.getName());
			if(name.startsWith("Formalisation")) {
				f.getParentFile().mkdirs();
				
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
