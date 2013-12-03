abstract sig Person {}

sig Coach, Player extends Person {}

sig Team {
	coach : one Coach,
	roster: some Player
}

---------------------Facts----------------------
//Coaches cannot coach more than one team

fact f_coach {
	Coach = Team.coach //every coach is associated with a team

	no disj t1, t2 : Team | t1.coach = t2.coach //coaches cannot coach more than one team
}

fact f_roster {
	// Player = Team.roster // every player is associated with a team
	all p: Person | one t: Team | p in t.coach or p in t.roster // every play is associated with one team
	all disj t1, t2 : Team |no t1.roster & t2.roster // players cannot play for two teams
	all disj t1, t2 : Team | #t1.roster = #t2.roster //every team has the same number of players
} 

run {} for 12 but exactly 3 Team
