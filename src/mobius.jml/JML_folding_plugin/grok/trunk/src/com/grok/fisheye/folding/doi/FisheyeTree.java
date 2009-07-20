/**
 * 
 */
package com.grok.fisheye.folding.doi;

import java.util.LinkedHashMap;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jface.text.Position;

import com.grok.fisheye.folding.java.JavaProjectionAnnotation;


/**
 * @author phosphorus
 *
 */
public class FisheyeTree {
	private FisheyeNode my_root = new FisheyeNode();
	private LinkedHashMap<JavaProjectionAnnotation, Position> my_annotation_map;
	
	/* @region constructors */
	public FisheyeTree() {
		
	}

	/* @region queries */
	

	protected LinkedHashMap getFoldingStructure() {
		return null;
		
	}
	
	/* @region commands */
	public void addAnnoation(JavaProjectionAnnotation an_annotation, Position a_position) {
		my_root.addNode(an_annotation, a_position);
	}
	
	protected void removeAnnotation(JavaProjectionAnnotation an_annotation) {
		my_root.removeAnnotation(an_annotation);
	}
	
	protected void updateInterest() {
		
	}
}
