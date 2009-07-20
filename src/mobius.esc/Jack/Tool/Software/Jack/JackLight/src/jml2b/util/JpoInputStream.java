//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jml2b.util;

import java.io.DataInput;
import java.io.DataInputStream;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.Hashtable;

/**
 * @author L. Burdy
 */
public class JpoInputStream {

	DataInput dis;
	Hashtable t;

	public JpoInputStream(DataInput bis, DataInputStream pool)
		throws IOException {
		dis = bis;
		int size = pool.readInt();
		t = new Hashtable(size);
		for (int i = 0; i < size; i++) {
			String s = pool.readUTF();
			int k = pool.readInt();
			t.put(new Integer(k), s);
		}
	}

	public String readUTF() throws IOException {
		return (String) t.get(new Integer(dis.readInt()));
	}

	public int readInt() throws IOException {
		return dis.readInt();
	}

	public boolean readBoolean() throws IOException {
		return dis.readBoolean();
	}

	public byte readByte() throws IOException {
		return dis.readByte();
	}

	public long getFilePointer() throws IOException {
		if (dis instanceof RandomAccessFile)
			return ((RandomAccessFile) dis).getFilePointer();
		else
			return -1;
	}

	/**
	 * @param lemmasFileIndex
	 */
	public void seek(long lemmasFileIndex) throws IOException {
		if (dis instanceof RandomAccessFile)
			 ((RandomAccessFile) dis).seek(lemmasFileIndex);
	}

}
