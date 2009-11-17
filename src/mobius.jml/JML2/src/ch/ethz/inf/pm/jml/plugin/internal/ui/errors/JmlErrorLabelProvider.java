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


package ch.ethz.inf.pm.jml.plugin.internal.ui.errors;

import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;

import ch.ethz.inf.pm.jml.plugin.JmlErrorElement;

/**
 * @author Paolo Bazzi
 *
 */
public class JmlErrorLabelProvider extends LabelProvider implements ITableLabelProvider, IColorProvider {

	public Image getColumnImage(Object element, int columnIndex) {
		return null;
	}

	public String getColumnText(Object element, int columnIndex) {
		JmlErrorElement jmlerr = (JmlErrorElement)element;
		switch(columnIndex)
		{
		case 0:
			return Integer.toString(jmlerr.getLineNr());
		case 1:
			return Integer.toString(jmlerr.getCharNr());
		case 2:
			return jmlerr.getMessage();
		case 3:
			return jmlerr.getFile().getName();
		case 4:
			String ref = jmlerr.getJmlReference();
			return ref!=null ? ref : "";
		}
		return null;
	}

	public Color getBackground(Object element) {
		return null;
	}

	public Color getForeground(Object element) {
		return null;
	}
}
