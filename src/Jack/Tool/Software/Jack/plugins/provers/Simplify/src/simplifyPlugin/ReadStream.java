//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package simplifyPlugin;

import java.io.IOException;
import java.io.InputStream;
import java.util.Vector;

class ReadStream extends Thread {

	Simplify simp;
	InputStream s;
	Vector readed;
	boolean continu;

	synchronized String read(byte[] ba) {
		if (ba == null) {
			if (!readed.isEmpty()) {
				return (String) readed.remove(0);
			}
		} else {
			readed.add(new String(ba));
		}
		return null;
	}

	ReadStream(Simplify s) {
		simp = s;
		this.s = s.getSimplify().getInputStream();
		continu = true;
		readed = new Vector();
	}

	void stopped() {
		continu = false;
	}

	boolean isAliv() {
		return continu || !readed.isEmpty();
	}

	public void run() {
		try {

			int len;
			byte[] ba;
			do {
				ba = new byte[len = s.available()];
				if (len != 0) {
					s.read(ba, 0, len);
					read(ba);
				} else {
					synchronized (s) {
						s.wait(100);
					}
				}
			} while (simp.isAlive() && continu);
			//Encore une lecture
			do {
				ba = new byte[len = s.available()];
				if (len != 0) {
					s.read(ba, 0, len);
					read(ba);
				}
			} while (len != 0);
			stopped();
		} catch (InterruptedException ie) {
			throw new InternalError("Exception " + ie.getMessage());
		} catch (IOException ioe) {
			throw new InternalError("Exception " + ioe.getMessage());
		}
	}

}