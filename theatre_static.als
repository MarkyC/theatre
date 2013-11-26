sig Seat {
    who : one Patron
}
sig Patron {
    ticket_for : one Seat
}
one sig Theatre {
    atrium : set Patron,
    seated : set Patron
}

fact no_double_booked_seats {
    no disj p1, p2 : Patron | p1.ticket_for != p2.ticket_for
}

fact unsold_seats {
    some s : Seats | s.who = {}
}

fact atrium_seat_disjoint {
    one t : Theatre | no (t.atrium & t.seated)
}

fact seated_patrons_have_tickets {
    one t : Theatre | some s : Seat | t.seated.ticket_for = s
}
