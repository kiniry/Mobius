package fr.inria.everest.coq.sugar.builder;

import prover.gui.builder.ProverFileWizard;

public class CoqFileWizard extends ProverFileWizard {
	public final static String extension = ".v";
    public final static String title = "New vernacular file";
    public final static String description = "Create a new vernacular file to edit in Coq.";
        
    public CoqFileWizard() {
		super(extension, title, description);
	}

 
}