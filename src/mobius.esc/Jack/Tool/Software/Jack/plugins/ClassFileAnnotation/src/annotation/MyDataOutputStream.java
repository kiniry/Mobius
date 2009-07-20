//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package annotation;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;

import jml2b.util.IOutputStream;

/**
 *
 *  @author L. Burdy
 **/
public class MyDataOutputStream extends DataOutputStream implements IOutputStream {

	public MyDataOutputStream(ByteArrayOutputStream baos) {
		super(baos);
	}


}
