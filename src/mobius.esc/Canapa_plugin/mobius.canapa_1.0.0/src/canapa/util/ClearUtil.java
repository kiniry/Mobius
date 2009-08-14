/*
 * Created on 2006-03-05
 *
 */
package canapa.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.StringBufferInputStream;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

public class ClearUtil {
	
	private static final String begin ="/*CANAPA*//*@";
	private static final String end = "@*/";
	private static final String canapa = "/*CANAPA*/";
	
	public static void clearCanapaAnnotations(IFile file){
		String s = fileToString(file);
		s = clearAnnotationsFromString(s);
		stringToFile(s, file);
	}
	
	private static void stringToFile(String string, IFile file) {
		try {
			InputStream is = new StringBufferInputStream(string);
			file.setContents(is, true, true, null);
		} catch (CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private static String fileToString(IFile file) {
		try {
			InputStream is = file.getContents();
			byte[] b = new byte[is.available ()];
			is.read(b);
			is.close();
			String result = new String (b);
			return result;
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		} catch (CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}
	}
	
	private static String clearAnnotationsFromString(String data) {
		while (true) {
			int s = data.indexOf(begin);
			
			if (s == -1)
				return data;
			
			int e = data.indexOf(end, s);
			
			if (e == -1)
				return data;
			
			data = data.substring(0, s) + data.substring(e + end.length() , data.length());
		}
	}

	/**
	 * @param string
	 */
	public static void commitCanapaAnnotations(IFile file) {
		String s = fileToString(file);
		s = clearCanapasFromString(s);
		stringToFile(s, file);
	}

	/**
	 * @param s
	 * @return
	 */
	private static String clearCanapasFromString(String data) {
		while (true) {
			int s = data.indexOf(canapa);
			
			if (s == -1)
				return data;
			
			data = data.substring(0, s) + data.substring(s + canapa.length() , data.length());
		}
	}
}
