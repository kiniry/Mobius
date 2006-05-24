//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/

package jpov.structure;

import java.io.IOException;

import jml2b.util.JpoInputStream;
import jml2b.util.JpoOutputStream;

/**
 * @author lburdy
 *
 * To change the template for this generated type comment go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
public class Field {

	private String name;

	public Field(JpoInputStream s) throws IOException {
		name = s.readUTF();
	}

	public void save(JpoOutputStream s) throws IOException {
		s.writeUTF(name);
	}

	/**
	 * @return
	 */
	public String getName() {
		return name;
	}

}
