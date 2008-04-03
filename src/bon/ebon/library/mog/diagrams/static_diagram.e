indexing
	description: "A static diagram."

class
	STATIC_DIAGRAM

inherit
	DIAGRAM
	
	SPECIFICATION_ELEMENT
	
creation
	make_static_diagram

feature -- Initialization

	make_static_diagram (a_name: STRING; 
											 a_comment: COMMENT; 
											 some_components: STATIC_COMPONENTS) is
			-- Initialize `Current'.
		require
			a_name /= Void
		do
			create my_name.make_from_string (a_name)
			create my_comment.make_from_list (a_comment)

			my_components := some_components.twin
		ensure
			name.is_equal (a_name)
			comment.is_equal (a_comment)
			components.is_equal (some_components)
		end

feature -- Access

	hash_code: INTEGER is
		do
			Result := my_name.hash_code
		end

	name: STRING is
			-- The name of this diagram.
		do
			Result := my_name.twin
		end

	comment: COMMENT is
			-- The comment applied to this diagram.
		do
			Result := my_comment.twin
		end

	components: STATIC_COMPONENTS is
			-- The static components contained in this diagram.
		do
			Result := my_components.twin
		end

feature -- Status report

	is_valid: BOOLEAN is
		do
			check false end
		end

	components_count: INTEGER is
			-- The number of components in `Current'.
		do
			Result := components.count
		end

feature -- Duplication

	copy (other: like Current) is
		do
			check false end
		end

feature -- Comparison

	is_equal (other: like Current): BOOLEAN is
		do
			Result := equal (my_name, other.my_name) and
				equal (my_comment, other.my_comment) and
				equal (my_components, other.my_components)
		end

feature -- Element change

	set_name (a_name: STRING) is
		require
			a_name /= Void
		do
			my_name := a_name.twin
		ensure
			name.is_equal (a_name)
		end

	set_comment (a_comment: COMMENT) is
		require
			a_comment /= Void
		do
			my_comment := a_comment.twin
		ensure
			comment.is_equal (a_comment)
		end

	set_components (some_components: STATIC_COMPONENTS) is
		do
			my_components.wipe_out
			components.append (some_components.twin)
		ensure
			components.is_equal (some_components)
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

feature -- Miscellaneous

feature -- Basic operations

feature -- Obsolete

feature -- Inapplicable

feature {STATIC_DIAGRAM} -- Implementation

	my_name: STRING
	my_comment: COMMENT
	my_components: STATIC_COMPONENTS

invariant

	my_name /= Void
	my_comment /= Void
	my_components /= Void

end -- class STATIC_DIAGRAM
