indexing
	description: "A class name and an optional list of actual generics."
	author: "Joseph Kiniry <kiniry@kindsoftware.com>"
	date: "$Date: 2005/12/21 14:06:18 $"
	revision: "$Revision: 1.2 $"

class
	CLASS_TYPE

inherit
	HASHABLE

creation
	make

feature -- Initialization

	make (a_class_name: STRING; 
				some_actual_generics: ACTUAL_GENERICS) is
			-- Initialize `Current'.
		require
			a_class_name /= Void and then not a_class_name.is_empty
		do
			my_class_name := a_class_name.twin
			my_actual_generics := some_actual_generics.twin
		ensure
			class_name.is_equal (a_class_name)
			my_actual_generics /= Void implies
				actual_generics.is_equal (some_actual_generics)
			my_actual_generics = Void implies actual_generics = Void
		end

feature -- Access

	class_name: STRING is
			-- The class name of `Current'.
		do
			Result := my_class_name.twin
		ensure
			Result /= Void and then	not Result.is_empty
		end
		
	actual_generics: ACTUAL_GENERICS is
			-- The actual generics of `Current'.
		do
			Result := my_actual_generics.twin
		end
		
	hash_code: INTEGER is
		do
			Result := my_class_name.hash_code
		end

feature -- Measurement

	actual_generic_count: INTEGER is
			-- The number of actual generics of `Current'.
		do
			if my_actual_generics /= Void then
				-- Result := my_actual_generics.count
				check false end
			else
				Result := 0
			end
		ensure
			Result >= 0
		end

feature -- Element change

	set_class_name (a_class_name: STRING) is
			-- Set class name of `Current'.
		require
			a_class_name /= Void and then not a_class_name.is_empty
		do
			my_class_name := a_class_name.twin
		ensure
			class_name.is_equal (a_class_name)
		end
		
	set_actual_generics (some_actual_generics: ACTUAL_GENERICS) is
			-- Set the actual generics of `Current'.
		do
			my_actual_generics := some_actual_generics.twin
		ensure
			some_actual_generics /= Void implies 
				actual_generics.is_equal (some_actual_generics)
		end

feature {CLASS_TYPE} -- Implementation

	my_class_name: STRING
	my_actual_generics: ACTUAL_GENERICS

invariant

	my_class_name_not_empty: my_class_name /= Void and then 
		not my_class_name.is_empty

end -- class CLASS_TYPE
