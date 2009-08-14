package engine;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.nio.channels.FileChannel;
import java.util.HashMap;
import java.util.Map;

import antlr.RecognitionException;

import test.JavaPrinter;

import jparse.FileAST;

import canapa.util.FixLocation;

public class ModifiedFile {

	File _file;
	Map _modifications = new HashMap();
	File _tempFile = null;
	
	public ModifiedFile(File file) {
		_file = file;
	}

	public File getFile() {
		return _file;
	}

	public int getLineOffset(int line) {
		Integer i = (Integer) _modifications.get(new Integer(line));
		if (i == null)
			return 0;
		return i.intValue();
	}

	public void increaseOffset(FixLocation loc) {
		Integer i = (Integer) _modifications.get(new Integer(loc.getLine()));
		if (i == null)
			i = new Integer(0);
		int di = i.intValue();
		di += loc.getSuggestion().length();
		_modifications.put(new Integer(loc.getLine()), new Integer(di));
	}

	public void saveModifications(FileAST fileAST) {
		final JavaPrinter printer = new JavaPrinter();
		File newFile;
		try {
			newFile = getTempFile();
			OutputStream os = new FileOutputStream(newFile);
			OutputStreamWriter out = new OutputStreamWriter(os);
			printer.compilationUnit(fileAST, out);
			_file = newFile;
		} catch (IOException e) {
			e.printStackTrace();
		} catch (RecognitionException e) {
			e.printStackTrace();
		}
	}

	private File getTempFile() {
		if (_tempFile != null) {
			_tempFile.delete();
		}
		try {
			_tempFile = File.createTempFile("jfu", "lja");
			_tempFile.deleteOnExit();
			return _tempFile;
		} catch (IOException e) {
			e.printStackTrace();
		}
		return null;
	}
}
