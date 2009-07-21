indexing
	description: "A specificaton of a cluster."

class
	CLUSTER_SPECIFICATION

inherit
	STATIC_COMPONENT
		rename
			is_equal as is_equal_component,
			copy as copy_component,
			bon_out as bon_out_component
		end

	STATIC_DIAGRAM
		redefine
			is_equal, copy,
			bon_out,
			canonicalize,
			hash_code,
			is_part_of, contains, is_disjoint,
			merge, intersect, subtract, symdif
		select
			is_equal, copy,
			bon_out
		end

creation
	make

feature -- Initialization

	make (a_name: STRING; 
			a_reused_flag: BOOLEAN;
			a_comment: COMMENT; 
			some_components: STATIC_COMPONENTS) is
			-- Initialize `Current'.
		require
			a_name /= Void
		do
			make_static_diagram (a_name, a_comment, some_components)

			set_reused (a_reused_flag)
		ensure
			reused = a_reused_flag
		end

feature -- Access

	hash_code: INTEGER is
		do
			check false end
		end

	reused: BOOLEAN is
			-- Is this cluster reusable?
		do
			Result := my_reused_flag
		end

feature -- Measurement

feature -- Status report

feature -- Status setting

feature -- Cursor movement

feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		do
		Result := is_equal_component (other) and is_equal (other) and
				equal (my_reused_flag, other.my_reused_flag)
		end

feature -- Element change

	set_reused (a_reused_flag: BOOLEAN) is
			-- Set the reused flag of `Current'.
		do
			my_reused_flag := a_reused_flag
		ensure
			reused = a_reused_flag
		end

feature -- Duplication

	copy (other: like Current) is
		do
			check false end
		end

feature -- Transformation

	canonicalize: like Current is
		do
			check false end
		end

feature -- Output

	bon_out: STRING is
		do
			check false end
		end

feature -- Status report
	
	is_part_of (other: like Current): BOOLEAN is
		do
			check false end
		end

	contains (other: like Current): BOOLEAN is
		do
			check false end
		end

	is_disjoint (other: like Current): BOOLEAN is
		do
			check false end
		end

feature -- Basic operations

	merge (other: like Current): like Current is
		do
			check false end
		end

	intersect (other: like Current): like Current is
		do
			check false end
		end

	subtract (other: like Current): like Current is
		do
			check false end
		end

	symdif (other: like Current): like Current is
		do
			check false end
		end

feature -- Removal

feature -- Resizing

feature -- Transformation

feature -- Conversion

feature -- Duplication

feature -- Miscellaneous

feature -- Basic operations

feature -- Obsolete

feature -- Inapplicable

feature {CLUSTER_SPECIFICATION} -- Implementation

	my_reused_flag: BOOLEAN

end -- class CLUSTER_SPECIFICATION
