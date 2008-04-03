indexing
	description: "A class type or a formal generic name."
	author: "Joseph Kiniry <kiniry@kindsoftware.com>"
	date: "$Date: 2005/12/21 14:05:38 $"
	revision: "$Revision: 1.1 $"

class
	BON_TYPE
	-- Should just be a COTUPLE [CLASS_TYPE, STRING].

inherit
	HASHABLE

creation
	make_class_type, make_formal_generic_name
	
feature -- Initialization

	make_class_type (a_class_type: CLASS_TYPE) is
			-- Initialize `Current'.
		require
			a_class_type /= Void
		do
			my_class_type := a_class_type.twin
		ensure
			class_type.is_equal (a_class_type)
		end
		
	make_formal_generic_name (a_formal_generic_name: STRING) is
			-- Initialize `Current'.
		require
			a_formal_generic_name /= Void and then
				not a_formal_generic_name.is_empty
		do
			my_formal_generic_name := a_formal_generic_name.twin
		ensure
			a_formal_generic_name /= Void and then
				formal_generic_name.is_equal (a_formal_generic_name)
		end

feature -- Access

	class_type: CLASS_TYPE is
			-- The class type of `Current'.
		do
			Result := my_class_type.twin
		end
		
	formal_generic_name: STRING is
			-- The formal generic name of `Current'.
		do
			Result := my_formal_generic_name.twin
		ensure
			Result /= Void implies not Result.is_empty
		end

	hash_code: INTEGER is
		do
			if my_class_type /= Void then
				Result := my_class_type.hash_code
			else
				Result := my_formal_generic_name.hash_code
			end
		end

feature -- Element change

	set_class_type (a_class_type: CLASS_TYPE) is
			-- Set the class type of `Current'.
		do
			my_class_type := a_class_type.twin
		ensure
			a_class_type /= Void implies class_type.is_equal (a_class_type)
			a_class_type = Void implies class_type = Void
		end
		
	set_formal_generic_name (a_formal_generic_name: STRING) is
			-- Set the formal generic name of `Current'.
		do
			my_formal_generic_name := a_formal_generic_name.twin
		ensure
			a_formal_generic_name /= Void implies 
				formal_generic_name.is_equal (a_formal_generic_name)
			a_formal_generic_name = Void implies formal_generic_name = Void
		end

feature {TYPE} -- Implementation

	my_class_type: CLASS_TYPE
	my_formal_generic_name: STRING

invariant

	my_class_type /= Void xor 
		(my_formal_generic_name /= Void and then not my_formal_generic_name.is_empty)

end -- class BON_TYPE
