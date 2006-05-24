//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.util;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Enumeration;
import java.util.Hashtable;

/**
 * @author L. Burdy
 */
public class JpoOutputStream implements IOutputStream {

	private DataOutputStream dos;
	private Hashtable t = new Hashtable();
	int nb = 0;

	public JpoOutputStream(OutputStream out) {
		dos = new DataOutputStream(out);
	}

	public void save(DataOutputStream dstr) throws IOException {
		dstr.writeInt(t.size());
		Enumeration e = t.keys();
		while (e.hasMoreElements()) {
			String element = (String) e.nextElement();
			dstr.writeUTF(element);
			dstr.writeInt(((Integer) t.get(element)).intValue());
		}
	}

	public void writeUTF(String str) throws IOException {
		Object value;
		if ((value = t.get(str)) != null)
			dos.writeInt(((Integer) value).intValue());
		else {
			t.put(str, new Integer(nb));
			dos.writeInt(nb++);
		}
	}

	public void flush() throws IOException {
		dos.flush();
	}

	public int size() {
		return dos.size();
	}

	public void write(byte[] b, int off, int len) throws IOException {
		dos.write(b, off, len);
	}

	public void write(int b) throws IOException {
		dos.write(b);
	}

	public void writeBoolean(boolean v) throws IOException {
		dos.writeBoolean(v);
	}

	public void writeByte(int v) throws IOException {
		dos.writeByte(v);
	}

	public void writeBytes(String s) throws IOException {
		dos.writeBytes(s);
	}

	public void writeChar(int v) throws IOException {
		dos.writeChar(v);
	}

	public void writeChars(String s) throws IOException {
		dos.writeChars(s);
	}

	public void writeDouble(double v) throws IOException {
		dos.writeDouble(v);
	}

	public void writeFloat(float v) throws IOException {
		dos.writeFloat(v);
	}

	public void writeInt(int v) throws IOException {
		dos.writeInt(v);
	}

	public void writeLong(long v) throws IOException {
		dos.writeLong(v);
	}

	public void writeShort(int v) throws IOException {
		dos.writeShort(v);
	}

	public void close() throws IOException {
		dos.close();
	}

	public void write(byte[] b) throws IOException {
		dos.write(b);
	}

}
