/*

Finish the specification of this notification concept,
including its events, scenarios, and operational principles.

*/ 

sig Resource {}

sig User {
	var reservations : set Resource
}

var sig Available in Resource {}

// Used resources: neither available nor reserved
fun Used : set Resource {
	Resource - Available - User.reservations
}

pred reserve[u : User, r : Resource] {
	// Make a reservation
	r in Available
	Available' = Available - r
	reservations' = reservations + u->r
}

pred cancel[u : User, r : Resource] {
	// Cancel a reservation
	r in u.reservations
	Available' = Available + r
	reservations' = reservations - u->r
}

pred use[u : User, r : Resource] {
	// Use a reserved resource
	r in u.reservations
	Available' = Available
	reservations' = reservations - u->r
}

pred cleanup {
	// Make all used resources available again
	some Used
	Available' = Available + Used
	reservations' = reservations
}

pred stutter {
	Available' = Available
	reservations' = reservations
}

fact {
	Available = Resource
	no reservations
	always {
		stutter
		or 
		cleanup
		or 
		(some u : User, r : Resource| reserve[u,r] or cancel[u,r] or use[u,r])
	}
}

// Validation

run Example {
	// Empty run to be used for simulation
}

run Scenario1 {
	// A user reserves a resource, uses it, and finally a cleanup occurs
	some u : User, r : Resource | (reserve[u,r]; use[u,r]; cleanup)
} expect 1

run Scenario2 {
	// A user reserves a resource, cancels the reservation, and reserves again
	some u : User, r : Resource | (reserve[u,r]; cancel[u,r]; reserve[u,r])
} expect 1

run Scenario3 {
	// A user reserves two resources, cancels one, uses the other, and finally a cleanup occurs
	some u : User, disj r1, r2 : Resource | (
		reserve[u,r1]; reserve[u,r2]; cancel[u,r1]; use[u,r2]; cleanup )
} expect 1

run Scenario4 {
	// Two users try to reserve the same resource
	some disj u1, u2 : User, r : Resource | eventually (r in u1.reservations and reserve[u2,r])
} expect 0

run Scenario5 {
	// Eventually a cleanup is performed twice in a row
	eventually (cleanup; cleanup)
} expect 0

// Verification

check OP1 {
	// Reserved resources aren't available
	always no User.reservations & Available
}

check OP2 {
	// The system starts in a cleaned state
	no Used
}

check OP3 {
	// After a cleanup all unreserved resources are available
	always (cleanup implies after Available = Resource - User.reservations)
}

check OP4 {
	// A cleanup cannot affect existing reservations
	always (cleanup implies reservations' = reservations)
}

check OP5 {
	// Cancel undoes reserve
	always all u : User, r : Resource | (reserve[u,r]; cancel[u,r]) implies
		(Available'' = Available and reservations'' = reservations)
}

check OP6 {
	// Used resources were reserved before
	always all u : User, r : Resource | use[u,r] implies once reserve[u,r]
}

check OP7 {
	// Used resources can only be reserved again after a cleanup
	always all r : Resource | (some u : User | use[u,r]) implies
		after (cleanup releases no u : User | reserve[u,r])
}

check OP8 {
	// If a cleanup occurs some resource was used before
	always (cleanup implies once some u : User, r : Resource | use[u,r])
}

check OP9 {
	// Used resources were not canceled since being reserved
	always all u : User, r : Resource | use[u,r] implies
		before ((not cancel[u,r]) since reserve[u,r])
}

check OP10 {
	// Reserved resources can be used while not used or canceled
	always all u : User, r : Resource |
		(before ((not use[u,r] and not cancel[u,r]) since reserve[u,r])) implies r in u.reservations
}

check OP11 {
	// The first event to occur will be a reservation
	(always stutter) or (stutter until some u : User, r : Resource | reserve[u,r])
}

check OP12 {
	// If cleanups and cancels never occur the available resources keep diminishing
	(always (not cleanup and no u : User, r : Resource | cancel[u,r])) implies
		always Available' in Available
}
