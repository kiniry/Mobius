indexing
	description: "An elided static component."
	author: "Joseph R. Kiniry <kiniry@kindsoftware.com>"
	date: "$Date: 2005/12/21 14:06:18 $"
	revision: "$Revision: 1.2 $"

class
	UNSPECIFIED_STATIC_COMPONENT

inherit
	STATIC_COMPONENT
		rename
			make_ellipses as make_unspecified
		end
	
creation
	make_unspecified

feature -- Access

	hash_code: INTEGER is
		do
			Result := 0
		end
		
feature -- Status report

	-- All routines must return TRUE because we simply do not have enough
	-- information to determine the relationship between elided static
	-- components and all contracts must be fulfilled.  All basic operations
	-- currently return Current.  TODO: must reevaluate these decisions to
	-- determine if they are necessary and/or sound.

	is_part_of (other: like Current): BOOLEAN is
		do
			Result := TRUE
		end

	contains (other: like Current): BOOLEAN is
		do
			Result := TRUE
		end

	is_disjoint (other: like Current): BOOLEAN is
		do
			Result := TRUE
		end

feature -- Basic operations

	merge (other: like Current): like Current is
		do
			Result := Current
		end

	intersect (other: like Current): like Current is
		do
			Result := Current
		end

	subtract (other: like Current): like Current is
		do
			Result := Current
		end

	symdif (other: like Current): like Current is
		do
			Result := Current
		end
		
feature -- Transformation

	canonicalize: like Current is
		do
			Result := Current.twin
		end

end -- class UNSPECIFIED_STATIC_COMPONENT
