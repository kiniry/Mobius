//******************************************************************************
/* Copyright (c) 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.util;

import java.io.IOException;

/**
 *
 *  @author L. Burdy
 **/
public interface IOutputStream {

	void writeUTF(String string) throws IOException;

	void writeByte(int tag) throws IOException;

	void writeInt(int tag) throws IOException;

	void writeBoolean(boolean b) throws IOException;

}
