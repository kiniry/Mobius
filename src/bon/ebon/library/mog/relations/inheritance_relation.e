indexing
	description: "The (possibly labeled) relationship between a child %
							% and a/some parent class(es)."

class
	INHERITANCE_RELATION

inherit
	STATIC_RELATION
		redefine
			bon_out
		end

creation
	make

feature -- Initialization

	make(a_child: STATIC_REF;
			a_multiplicity: INTEGER;
			a_parent: STATIC_REF;
			a_label: STRING) is
			-- Initialize `Current' with specified child, multiplicity,
			-- parent, and label.
		require
			a_child /= Void
			a_parent /= Void
			a_multiplicity >= 0
		do
			my_child := a_child.twin
			my_multiplicity := a_multiplicity
			my_parent := a_parent.twin
			my_label := a_label.twin
		ensure
			child.is_equal (a_child)
			multiplicity = a_multiplicity
			parent.is_equal (a_parent)
			label /= Void implies label.is_equal (a_label)
		end

feature -- Access

	child: STATIC_REF is
			-- The child of the inheritance relation.
		do
			Result := my_child.twin
		ensure
			Result /= Void
		end

	multiplicity: INTEGER is
			-- The multiplicity of this inheritance relation.
		do
			Result := my_multiplicity
		ensure
			Result >= 0
		end

	parent: STATIC_REF is
			-- The parent of this inheritance relation.
		do
			Result := my_parent.twin
		ensure
			Result /= Void
		end

	label: STRING is
			-- The optional label on this inheritance relation.
		do
			Result := my_label.twin
		end

	hash_code: INTEGER is
		do
			Result := parent.hash_code + child.hash_code
		end

feature -- Transformation

	canonicalize: like Current is
		do
			check false end
		end

feature -- Output

	bon_out: STRING is
		do
			if ellipses then
				Result := Precursor
			else
				Result := my_child.bon_out
				Result.append (" inherit ")
				if multiplicity > 0 then
					Result.append (" { ")
					Result.append (my_multiplicity.out)
					Result.append (" } ")
				end
				Result.append (parent.bon_out)
				if label /= Void then
					Result.append (" ")
					Result.append (label)
				end
			end
		ensure then
			Result.count >= 11
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

feature { INHERITANCE_RELATION } -- Implementation

	my_child: STATIC_REF
  my_multiplicity: INTEGER
  my_parent: STATIC_REF
  my_label: STRING
  
invariant
	
	my_child /= Void
	my_multiplicity >= 0
	my_parent /= Void

end -- class INHERITANCE_RELATION
