package bonIDE.diagram.custom;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.gmf.runtime.diagram.ui.figures.ResizableCompartmentFigure;
import org.eclipse.gmf.runtime.draw2d.ui.mapmode.IMapMode;

public class VeryThinResizableCompartmentFigure extends ResizableCompartmentFigure {

	public VeryThinResizableCompartmentFigure(String compartmentTitle, IMapMode mm) {
		super(compartmentTitle, mm);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.gmf.runtime.diagram.ui.figures.ResizableCompartmentFigure#getMinClientDimension()
	 */
	@Override
	public Dimension getMinClientDimension() {
		return new Dimension(5, 1);
	}		
}
