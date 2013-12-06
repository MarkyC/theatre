//CSE 4312 Assignment 1
//Name: Marco Cirillo (mmmarcooo@gmail.com)
//Name: Robert Mete (metero@teksavvy.com)
//Name: Pathmaraj Pathmalingam (bhathu_thomean@live.ca)

open util/ordering[Step]

abstract sig Person {}

sig Step {} 

sig Coach, Player extends Person {}

sig Team {
        coach: Coach one -> Step,
        roster: Player
}

---------------------Facts----------------------
//Coaches cannot coach more than one team

fact f_coach {
        //Coach = Team.coach //every coach is associated with a team
        no disj t1, t2 : Team | t1.coach = t2.coach //coaches cannot coach more than one team
}

pred p_coach[st : Step] {
        all p: Person | one t: Team | p in t.coach.st  // every coach is associated with one team
} 

// the state invariant 
pred Invariant [st : Step] {
        p_coach[st]
}

//Trade Coach
pred trade_coach [t1 : Team, t1r : set Coach, t2 : Team, t2r : set Coach, st : Step] {
        // pre-condition
        one st.next // a next step exists
        t1r in t1.coach.st // can only trade a coach you have on your team
        t2r in t2.coach.st // same as above
        t1 != t2 // not the same team for trade
        #t1r = 1 // only 1 coach should be in the trade deal

        // post-condition
        let st_prime = st.next {
                t1.coach.st_prime = t1.coach.st - t1r + t2r // t1's new coach
                t2.coach.st_prime = t2.coach.st - t2r + t1r // t2's new coach
        }

        // frame - if a team is not involved in the trade, the roster remains the same
        let st_prime = st.next {
                all t : Team - (t1 + t2) | t.coach.st_prime = t.coach.st 
        }
}

// predicate 
pred p_init [st : Step] {
        all p : Player | one t : Team | p in t.roster// all players are on exactly one team
        no disj t1, t2 : Team | #t1.roster != #t2.roster // all teams are of the same size
}

// run {} for 12 but exactly 3 Team

/*
run {
        all st : Step | Invariant[st]
} for 12 but exactly 3 Step, exactly 3 Team
*/

pred p_run {
        some st : Step - last, t1, t2 : Team, t1r, t2r : Coach| (trade_coach[t1, t1r, t2, t2r, st] and Invariant [st])
        all st: Step | Invariant[st]
}

assert a_init_establishes_invariant {
        p_init[first] => Invariant[first]
}

// checking operation closure
assert a_trade_close {
        all st : Step - last, t1, t2 : Team, t1r, t2r : set Coach {
                Invariant[st] && trade_coach[t1, t1r, t2, t2r, st] => Invariant[st.next]
        }
}

check a_trade_close for 13 but exactly 3 Team, exactly 2 Step

// checking operation closure
// starting with legal state, we should have a legal solution next
assert a_trade_close2 {
        all t1, t2 : Team, t1r, t2r : set Coach {
                Invariant[first] && trade_coach[t1, t1r, t2, t2r, first] => Invariant[first.next]
        }
}

check a_trade_close2 for 13 but exactly 3 Team, exactly 2 Step

// checking operation effectiveness
pred p_trade_effective {
        some st : Step | some t1, t2 : Team, t1r, t2r : set Coach | Invariant[st] && trade_coach[t1, t1r, t2, t2r, st]
        all st: Step | Invariant[st]
}

run p_trade_effective for 12 but exactly 2 Team, exactly 2 Step

pred p_trade_effective2 {
  some t1, t2 : Team, t1r, t2r : set Coach | Invariant[first] && trade_coach[t1, t1r, t2, t2r, first]
  all st: Step | Invariant[st]
}

run p_trade_effective2 for 12 but exactly 2 Team, exactly 2 Step

// run p_run for 12 but exactly 2 Player, exactly 3 Step, exactly 2 Team

// test initialization
run { 
        p_init[first] 
} for 12 but exactly 2 Player, exactly 1 Step, exactly 2 Team

// test initialization
run {
        p_init[first] 
} for 20 but exactly 6 Player, exactly 3 Team, exactly 1 Step

check a_init_establishes_invariant for 20 but exactly 6 Player, exactly 3 Team, exactly 1 Step
