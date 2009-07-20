//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package util;

/**
 *
 *  @author L. Burdy
 **/
public class ByteArray {

	public static byte[] concat(byte[] a, byte[] b) {
		byte[] res = new byte[a.length + b.length];
		int i = 0;
		for (; i < a.length; i++)
			res[i] = a[i];
		for (; i < a.length + b.length; i++)
			res[i] = b[i - a.length];
		return res;
	}

	public static byte[] add(int pos, byte b, byte[] a) {
		byte[] res = new byte[a.length + 1];
		for (int i = 0; i < a.length + 1; i++) {
			if (i == pos)
				res[i] = b;
			else
				res[i] = a[i - (i < pos ? 0 : 1)];
		}
		return res;
	}

	public static byte[] addShort(short b, byte[] a) {
		if (a == null)
			return new byte[] { 0x00, 0x00 };
		byte[] res = new byte[a.length + 2];
		res[0] = (byte) (b / 256);
		res[1] = (byte) (b % 256);
		for (int i = 2; i < a.length + 2; i++) {
			res[i] = a[i - 2];
		}
		return res;
	}

	public static byte[] addShortEnd(short b, byte[] a) {
		if (a == null)
			return new byte[] { 0x00, 0x00 };
		byte[] res = new byte[a.length + 2];
		for (int i = 0; i < a.length; i++) {
			res[i] = a[i];
		}
		res[a.length] = (byte) (b / 256);
		res[a.length+1] = (byte) (b % 256);
		return res;
	}

}
