indexing
	description: "A set of scenario entries."

class
	SCENARIO_ENTRIES

inherit
	MOG_SET [SCENARIO_ENTRY]

creation
	make, make_set, make_optional_rest, make_optional_first,
	make_from_set, make_from_list

end -- class SCENARIO_ENTRIES
