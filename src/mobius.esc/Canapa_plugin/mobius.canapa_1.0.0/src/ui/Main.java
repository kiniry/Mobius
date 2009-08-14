package ui;

import input.SuggestReporterImpl;
import input.intf.SuggestReporter;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.channels.FileChannel;
import java.util.Iterator;
import java.util.Map;

import engine.ModifiedFile;
import engine.Modifier;
import logs.Log;
import logs.LogType;

/**
 * @author mci
 */
public class Main {
	private static boolean changed = false;
	public static String volume = "";
	public static void main(String[] args) {
		System.out.println("CANAPA");
		System.out.println("Completely Automated Non-null Annotation Propagating Application");
		System.out.println("Version 1.0");
		System.out.println("");
		//System.setProperty("simplify", "E:\\workspace-mobius\\CanapaPlugin\\libs/Simplify-1.5.4.exe");
		for (int i = 0; i < args.length;i++){
			System.out.println(args[i]);
		}
		do {
			SuggestReporter rep = new SuggestReporterImpl();
			rep.addListener(new Modifier());
			Log.println(LogType.UI, "processing ...");
			changed = false;
			volume = "";
			for (int i = 0; i < args.length; i++){
				if ("-file".equals(args[i]) && i < args.length){
					String path =args[i+1];
					if (!path.startsWith("/")){
						//looking only for windows-style paths
						if (path.length() > 2 && path.charAt(1) == ':'){
							volume = path.substring(0, 2);
						}

					}
				}
			}
			rep.run(runESCJava(args));
			changed = false;
			Log.println(LogType.UI, "processing ... done");
		} while (changed);
		
		System.out.println("done");
	}


	void process(String filename, SuggestReporter rep) {
		try {
			rep.runFromFile(filename); //this file should contain escJava output
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void saveResults(Iterator it) {
		while (it.hasNext()) {
			changed = true;
			Map.Entry entry = (Map.Entry)it.next();
			Log.println(LogType.UI, "modifying " + entry.getKey() + " ...");
			String name = (String)entry.getKey();
			ModifiedFile mf = (ModifiedFile)entry.getValue();
			
			File original = new File(name);
			File backup = new File(name + ".bak");
			try {
				if (!backup.exists())
					copyFile(original, backup);
				copyFile(mf.getFile(), original);
			} catch (Exception e) {
				e.printStackTrace();
			}
			Log.println(LogType.UI, "modifying " + entry.getKey() + " ... done");
		}
	}
	
	private static void copyFile(File in, File out) throws Exception {
	     FileChannel sourceChannel = new
	          FileInputStream(in).getChannel();
	     FileChannel destinationChannel = new
	          FileOutputStream(out).getChannel();
	     sourceChannel.transferTo(0, sourceChannel.size(), destinationChannel);
	     // or
	     //  destinationChannel.transferFrom(sourceChannel, 0, sourceChannel.size());
	     sourceChannel.close();
	     destinationChannel.close();
	}
	
	private static String runESCJava(String[] parameters) {
		PrintStream tmp = System.out;
		
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream hacked = new PrintStream(baos);
		Log.println(LogType.UI, "running esc java ... ");
		System.setOut(hacked);
		
		escjava.Main.compile(parameters);

		String out = baos.toString();
		System.setOut(tmp);
		Log.println(LogType.UI, "running esc java ... done");
		Log.println(LogType.UI, out);
		return out;
	}
}
