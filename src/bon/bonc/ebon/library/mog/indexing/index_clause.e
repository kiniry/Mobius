indexing
	description: "An index clause consisting of a property and its values."

class
	INDEX_CLAUSE

inherit
	HASHABLE
		redefine
			-- ANY
			copy, is_equal,
			-- HASHABLE
			hash_code
		end

creation
	make_pair

feature -- Initialization

	make_pair (a_property: STRING; a_value: STRING_LIST) is
			-- Initializes `Current'
		require
			a_property /= Void
		do
			my_property := a_property.twin
			my_value := a_value.twin
		ensure
			property.is_equal (a_property)
			value.is_equal (a_value)
		end

feature -- Access

	property: STRING is
		do
			Result := my_property.twin
		end

	value: STRING_LIST is
		do
			Result := my_value.twin
		end

	hash_code: INTEGER is
		do
			Result := property.hash_code
		end

feature -- Duplication

	copy (other: like Current) is
		do
			check false end
		end

feature -- Comparison
	
	is_equal (other: like Current): BOOLEAN is
		do
			Result := property.is_equal (other.property) and
				(value /= Void implies value.is_equal (other.value))
		end

feature -- Element change

	set_property (a_property: STRING) is
		require
			a_property /= Void
		do
			my_property := a_property.twin
		ensure
			property.is_equal (a_property)
		end

	set_value (a_value: STRING_LIST) is
		do
			my_value := a_value.twin
		ensure
			value /= Void implies value.is_equal (a_value)
		end

feature {INDEX_CLAUSE} -- Implementation

	my_property: STRING
	my_value: STRING_LIST

invariant

	property /= Void

end -- class INDEX_CLAUSE
