/*
 * This file is part of the JML2 Eclipse Plug-in Project.
 *
 * Copyright (C) 2003-2008 Swiss Federal Institute of Technology Zurich
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Paolo Bazzi, Summer 2006
 * 
 */

package ch.ethz.inf.pm.jml.plugin.internal.ui.properties;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.FormColors;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.SharedScrolledComposite;

/**
 * @author Paolo Bazzi
 * 
 */

public class ScrolledPropPageContent extends SharedScrolledComposite {
	private FormToolkit fToolkit;
	
	public ScrolledPropPageContent(Composite parent) {
		this(parent, SWT.V_SCROLL | SWT.H_SCROLL);
	}
	
	public ScrolledPropPageContent(Composite parent, int style) {
		super(parent, style);
		
		setFont(parent.getFont());
		
		FormColors colors= new FormColors(parent.getDisplay());
		colors.setBackground(null);
		colors.setForeground(null);
		
		fToolkit= new FormToolkit(colors);
		
		//setExpandHorizontal(true);
		//setExpandVertical(true);
		
		Composite body= new Composite(this, SWT.NONE);
		body.setFont(parent.getFont());
		setContent(body);
	}
	
	public Composite getBody() {
		return (Composite) getContent();
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.swt.widgets.Widget#dispose()
	 */
	@Override
	public void dispose() {
		fToolkit.dispose();
		super.dispose();
	}
	
	public void adaptChild(Control childControl) {
		fToolkit.adapt(childControl, true, true);
	}
}
