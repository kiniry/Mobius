//******************************************************************************
/* Copyright (c) 2005 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.structure.java;

public interface IType {
	public int getTag();
	public jml2b.structure.java.AClass getRefType();
	public jml2b.structure.java.Type getElemType();
}
