//CSE 4312 Assignment 1
//Name: Marco Cirillo (mmmarcooo@gmail.com)
//Name: Robert Mete (metero@teksavvy.com)
//Name: Pathmaraj Pathmalingam (bhathu_thomean@live.ca)

sig Seat {
	/// 4. There is at most one Patron in a given Seat
    who : lone Patron
}
sig Patron {
	/// 1. Every Patron has a ticket_for one Seat
	/// 4. each Patron is in at most one Seat
    ticket_for : lone Seat  
}
one sig Theatre {
    atrium : set Patron,
    seated : set Patron
}

fact no_double_booked_seats {
    /// 1. no two distinct Patrons have a ticket_for the same Seat
    no disj p1, p2 : Patron | p1.ticket_for != p2.ticket_for
}

fact unsold_seats {
	/// 2. It is not necessary that every Seat be covered
    some s : Seat | no s.who 
	some p : Patron | no p.ticket_for                 //LOOK HERE: 1.)I think this conflicts with rule #1, which is "Every patron needs a ticket"
}

fact atrium_seat_disjoint {
	/// 3. The sets of Patrons in the atrium and seated are disjoint
    one t : Theatre | no (t.atrium & t.seated)  //LOOK HERE: 2.)I think this is saying that patrons cannot be in the atrium or seated....ever. 
    						//LOOK HERE: We need to include the cases when they can be in either atrium or seated. Should be 3 cases total.
}

/// 3. there may be Patrons who are in neither set
///    (atrium and seated do not necessarily partition Patron)

fact seated_patrons_have_tickets {
    //one t : Theatre | some s : Seat | t.seated.ticket_for = s

	/// 5. The Patrons in seated are exactly those who are in a Seat.
	all s : Seat | one t : Theatre | s.who in t.seated               //3.)LOOK HERE: should this be s.who == t.seated ?

	/// 6. Every seated Patron has a ticket_for the Seat the Patron is in 
	///    (e.g., is who is in that Seat).
    all p : Patron | one s : Seat  | s.who = p and p.ticket_for = s
}

//fun ticket_for: Seat -> Patron {~who}

/// 7. returns the set of Seats in which no Patron is sitting
fun empty : set Seat {
	Seat - { e : Seat | no e.who}
}

/// 8. returns the set of Seats for which no ticket has been sold 
///    (that is, the Seats no Patron has a ticket_for).
/*fun unsold : set Seat {
	all p : Patron | no p.ticket_for
}*/
fun unsold : set Seat {
	{ s : Seat | s.who in Patron - { u : Patron | no u.ticket_for} }
}

/// 9. the unsold seats are a subset of the empty seats, 
///    and check this assertion for a universe of (maximum) 
///    size 8 elements in each top-level signature.
assert Consistent {
	unsold in empty
}

/// 9. check this assertion for a universe of (maximum) size 8 
///    elements in each top-level signature.
check Consistent for 8

/// 10. ensures that some Patrons in the atrium, some Patrons are seated, 
///     and some Patrons are in neither set (they're outside the Theater).
pred people_can_be_anywhere {
	some p : Patron | one t : Theatre | p in t.seated
	some p : Patron | one t : Theatre | p in t.atrium
	some p : Patron | one t : Theatre | p not in t.seated and p not in t.atrium

	no p : Patron | one t : Theatre | p in t.seated and p not in t.seated
	no p : Patron | one t : Theatre | p in t.atrium and p not in t.atrium
}

/// 10. Run this predicate for a universe of (maximum) size 8 
///  	elements in each top-level signature
run people_can_be_anywhere for 8 


