indexing
	description: "A formal generic parameter of a class with optional class type."

class
	FORMAL_GENERIC

inherit
	HASHABLE

	BON_TEXT

	CANONICALIZABLE

creation
	make

feature -- Initialization

	make (a_name: STRING;
				a_class_type: CLASS_TYPE) is
			-- Initialize `Current'.
		require
			a_name /= Void
		do
			my_name := a_name.twin
			my_class_type := a_class_type.twin
		ensure
			name.is_equal (a_name)
			equal (class_type, a_class_type)
		end

feature -- Access

	hash_code: INTEGER is
		do
			Result := name.hash_code
		end

	name: STRING is
			-- The name of `Current'.
		do
			Result := my_name.twin
		end
	
	class_type: CLASS_TYPE is
			-- The optional class type of `Current'.
		do
			Result := my_class_type.twin
		end

feature -- Element change

	set_name (a_name: STRING) is
			-- Set the name of `Current'.
		require
			a_name /= Void and then not a_name.is_empty
		do
			my_name := a_name.twin
		ensure
			name.is_equal (a_name)
		end

	set_class_type (a_class_type: CLASS_TYPE) is
			-- Set the class type of `Current'.
		do
			my_class_type := a_class_type.twin
		ensure
			class_type.is_equal (a_class_type)
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

feature {FORMAL_GENERIC} -- Implementation

	my_name: STRING
	my_class_type: CLASS_TYPE

invariant

	name /= Void and then not name.is_empty

end -- class FORMAL_GENERIC
