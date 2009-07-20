//******************************************************************************
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: 
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jml2b.util;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

/**
 * @author M. Pavlova, L. Burdy
 */
public class ModifiableSet {
	
	
	private HashSet set ;

	
	public ModifiableSet() {
		set = new HashSet();
	}
	
	public ModifiableSet(HashSet set) {
		this.set = set;
	}
		
	public void addAll(Set another) {
		set.addAll(another);
	}
	
	public HashSet getSet() {
		return set;
	}

	public boolean containsOne(Set s) {
		Iterator i = s.iterator();
		while (i.hasNext()) {
			Object element = (Object) i.next();
			if (set.contains(element))
				return true;
		}
		return false;
	}
	
	

}
