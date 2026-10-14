sig User {
    follows: set User,
    sees: set Photo,
    posts: set Photo,
    suggested: set User
}

sig Influencer extends User {}

sig Photo {
    date: one Day
}

// 1. Assinatura Ad deduzida a partir do predicado seesAds
sig Ad extends Photo {}

sig Day {}

// 2. Facto original mantido (pode ser simplificado para "all p: Photo | one posts.p")
fact PostInjective {
    all p:Photo | some u:User | u->p in posts
    all p:Photo, u1, u2:User | u1->p in posts and u2->p in posts implies u1=u2
}

// 3. Blocos run e predicados corrigidos
run {}

pred SomePosts {
    some u:User, p:Photo | u->p in posts
}
run SomePosts for 3

pred Notirreflexive {
    some u:User| u->u not in follows
}
run Notirreflexive expect 1

pred irreflexive {
    all u:User | u->u not in follows
}

pred NotirreflexivePred {
    not irreflexive
}
run NotirreflexivePred expect 1

pred followers {
    all i:Influencer | all u:User | u->i in follows or u=i
}

pred seesAds {
    all u:User, p:Photo | u->p in sees implies
        p in Ad or (some f:User | u->f in follows and f->p in posts)
}