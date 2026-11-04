/*

Finish the specification of this notification concept,
including its events, scenarios, and operational principles.

*/ 

sig Event {}

sig User {
	var subscriptions : set Event,
	var notifications : set Event
}

pred stutter {
	subscriptions' = subscriptions
	notifications' = notifications
}

pred read[u : User] {
	// Read all notifications
	some u.notifications
	notifications' = notifications - u->Event
	subscriptions' = subscriptions
}

pred subscribe[u : User, e : Event] {
	// Subscribe an event
	e not in u.subscriptions
	subscriptions' = subscriptions + u->e
	notifications' = notifications
}

pred unsubscribe[u : User, e : Event] {
	// Unsubscribe from a event
	e in u.subscriptions
	subscriptions' = subscriptions - u->e
	notifications' = notifications - u->e
}

pred occur [e : Event] {
	// Occurrence of an event
	notifications' = notifications + (subscriptions.e)->e
	subscriptions' = subscriptions
}

fact {
	no subscriptions
	no notifications
	always {
		stutter or
		(some u : User | read[u]) or
		(some u : User, e : Event | subscribe[u,e] or unsubscribe[u,e]) or
		(some e : Event | occur[e])
	}
}

// Validation

run Example {
	// Empty run to be used for simulation
}

run Scenario1 {
	// An event is subscribed, then occurs, and the respective notification is read 
	some u : User, e : Event | (subscribe[u,e]; occur[e]; read[u])
} expect 1

run Scenario2 {
	// An event is subscribed, unsubscribed, and then occurs
	some u : User, e : Event | (subscribe[u,e]; unsubscribe[u,e]; occur[e])
} expect 1

run Scenario3 {
	// An event is subscribed by two users and then occurs
	some disj u1, u2 : User, e : Event | (subscribe[u1,e]; subscribe[u2,e]; occur[e])
} expect 1

run Scenario4 {
	// A user subscribes two events, then both occur, then unsubscribes one of them, and finally reads the notifications
	some u : User, disj e1, e2 : Event | (
		subscribe[u,e1]; subscribe[u,e2]; occur[e1]; occur[e2]; unsubscribe[u,e1]; read[u] )
} expect 1

run Scenario5 {
	// A user subscribes the same event twice in a row
	some u : User, e : Event | eventually (subscribe[u,e]; subscribe[u,e])
} expect 0

run Scenario6 {
	// Eventually an user reads notification twice in a row
	some u : User | eventually (read[u]; read[u])
} expect 0

// Verification 

check OP1 {
	// Users can only have notifications of subscribed events
	always all u : User | u.notifications in u.subscriptions
}

check OP2 {
	// Users can only read notifications if they have some subscription
	always all u : User | read[u] implies some u.subscriptions
}

check OP3 {
	// When an event occurs, no existing notifications are lost
	always all e : Event | occur[e] implies notifications in notifications'
}

check OP4 {
	// Unsubscribe undos subscribe
	always all u : User, e : Event | (subscribe[u,e]; unsubscribe[u,e]) implies
		(subscriptions'' = subscriptions and notifications'' = notifications)
}

check OP5 {
	// Notify is idempotent
	always all e : Event | (occur[e]; occur[e]) implies
		(subscriptions'' = subscriptions' and notifications'' = notifications')
}

check OP6 {
	// It's impossible to read notifications before some event is subscribed
	(some u : User, e : Event | subscribe[u,e]) releases (no u : User | read[u])
}

check OP7 {
	// After notifications are read, it is only possible to read again after some notification on a subscribed event occurs
	always all u : User | read[u] implies
		after ((some e : u.subscriptions | occur[e]) releases not read[u])
}
