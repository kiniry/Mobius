indexing
	description: "The relationship between a client and a/some supplier(s)."

class
	CLIENT_RELATION

inherit
	STATIC_RELATION
		redefine
			bon_out
		end

creation
	make

feature -- Initialization

	make (a_client: STATIC_REF;
				some_client_entities: CLIENT_ENTITIES;
				a_type_mark: TYPE_MARK;
				a_supplier: STATIC_REF;
				a_semantic_label: STRING) is
			-- Initialize `Current'.
		require
			a_client /= Void
			a_supplier /= Void
		do
			my_client := a_client.twin
--			if my_client_entities /= Void then
--				create my_client_entities.make (some_client_entities)
--			end
			my_type_mark := a_type_mark.twin
			my_supplier := a_supplier.twin
			my_semantic_label := a_semantic_label.twin
		ensure
			client.is_equal (a_client)
--			some_client_entities /= Void implies client_entities.is_equal (some_client_entities)
--			some_client_entities = Void implies client_entities = Void
			a_type_mark /= Void implies type_mark.is_equal (a_type_mark)
			a_type_mark = Void implies type_mark = Void
			supplier.is_equal (a_supplier)
			a_semantic_label /= Void implies semantic_label.is_equal (a_semantic_label)
			a_semantic_label = Void implies semantic_label = Void
		end

feature -- Access

	hash_code: INTEGER is
		do
			Result := client.hash_code + supplier.hash_code
		end

	client: STATIC_REF is
			-- Returns the client static reference of this client relation.
		do
			Result := my_client.twin
		ensure
			Result /= Void
		end

	client_entities: CLIENT_ENTITIES is
			-- Returns the client entities associated with this client relation.
		do
			Result := my_client_entities.twin
		end
		
	type_mark: TYPE_MARK is
			-- Returns the type mark of this client relation.
		do
			Result := my_type_mark.twin
		end
		
	supplier: STATIC_REF is
			-- Returns the supplier static reference of this client relation.
		do
			Result := my_supplier.twin
		ensure
			Result /= Void
		end
		
	semantic_label: STRING is
			-- The semantic label on this client relation.
		do
			Result := my_semantic_label.twin
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
				Result := "Client "
				Result.append (my_client.bon_out)
				Result.append (" ")
				if my_client_entities /= Void then
					-- Result.append (my_client_entities.bon_out)
					Result.append (" ")
				end
				if my_type_mark /= Void then
					Result.append (my_type_mark.bon_out)
					Result.append (" ")
				end
				Result.append (my_supplier.bon_out)
				if my_semantic_label /= Void then
					Result.append (my_semantic_label)
				end
			end
		ensure then
			Result.count >= 10
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

feature {CLIENT_RELATION} -- Implementation

	my_client: STATIC_REF
	my_client_entities: CLIENT_ENTITIES
	my_type_mark: TYPE_MARK
	my_supplier: STATIC_REF
	my_semantic_label: STRING

invariant

	client_non_void: my_client /= Void
	supplier_non_void: my_supplier /= Void

end -- class CLIENT_RELATION
