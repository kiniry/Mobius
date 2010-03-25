package bonIDE.diagram.custom;

import org.eclipse.draw2d.PolygonDecoration;
import org.eclipse.draw2d.geometry.PointList;

public class AggregationConnection extends DoubleLineConnection {
	public AggregationConnection() {
		super();

		setLineWidth(1);		

		PolygonDecoration curlyBrace = new PolygonDecoration();
		PointList bracePoints = new PointList();		

		bracePoints.addPoint(-18, 0);
		bracePoints.addPoint(-14, 2);
		bracePoints.addPoint(-13, 4);
		bracePoints.addPoint(-13, 21);
		bracePoints.addPoint(-12, 23);
		bracePoints.addPoint(-10, 25);
		bracePoints.addPoint(-7, 26);
		bracePoints.addPoint(-3, 26);
		bracePoints.addPoint(-5, 25);
		bracePoints.addPoint(-7, 23);
		bracePoints.addPoint(-8, 21);
		bracePoints.addPoint(-8, 6);
		bracePoints.addPoint(-10, 2);
		bracePoints.addPoint(-14, 0);
		bracePoints.addPoint(-10, -2);
		bracePoints.addPoint(-8, -6);
		bracePoints.addPoint(-8, -21);
		bracePoints.addPoint(-7, -23);
		bracePoints.addPoint(-5, -25);
		bracePoints.addPoint(-3, -26);
		bracePoints.addPoint(-7, -26);
		bracePoints.addPoint(-10, -25);
		bracePoints.addPoint(-12, -23);
		bracePoints.addPoint(-13, -21);
		bracePoints.addPoint(-13, -4);
		bracePoints.addPoint(-14, -2);
		bracePoints.addPoint(-18, 0);
		
//		bracePoints.addPoint(0, 0);
//		bracePoints.addPoint(4, 2);
//		bracePoints.addPoint(5, 4);
//		bracePoints.addPoint(5, 21);
//		bracePoints.addPoint(6, 23);
//		bracePoints.addPoint(8, 25);
//		bracePoints.addPoint(11, 26);
//		bracePoints.addPoint(15, 26);
//		bracePoints.addPoint(13, 25);
//		bracePoints.addPoint(11, 23);
//		bracePoints.addPoint(10, 21);
//		bracePoints.addPoint(10, 6);
//		bracePoints.addPoint(8, 2);
//		bracePoints.addPoint(4, 0);
//		bracePoints.addPoint(8, -2);
//		bracePoints.addPoint(10, -6);
//		bracePoints.addPoint(10, -21);
//		bracePoints.addPoint(11, -23);
//		bracePoints.addPoint(13, -25);
//		bracePoints.addPoint(15, -26);
//		bracePoints.addPoint(11, -26);
//		bracePoints.addPoint(8, -25);
//		bracePoints.addPoint(6, -23);
//		bracePoints.addPoint(5, -21);
//		bracePoints.addPoint(5, -4);
//		bracePoints.addPoint(4, -2);
//		bracePoints.addPoint(0, 0);				
		
		curlyBrace.setTemplate(bracePoints);
		curlyBrace.setScale(0.70, 0.70);
		curlyBrace.setFill(true);
		curlyBrace.setLineWidth(1);

		setSourceDecoration(curlyBrace);		
	}
}
