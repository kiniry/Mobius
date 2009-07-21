indexing
	description: "A set of creation entries."

class
	EVENT_ENTRIES

inherit
	MOG_SET [EVENT_ENTRY]

creation
	make, make_set, make_optional_rest, make_optional_first,
	make_from_set, make_from_list

end -- class EVENT_ENTRIES
