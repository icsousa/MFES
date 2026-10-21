sig Person {
    teaches : set Course,
    enrolled : set Course,
    worksOn : set Project
}

sig Professor, Student in Person {}

sig Course {
    proposes : set Project,
    grades : Person -> lone Grade
}

sig Project {}

sig Grade {}

pred mult1 {
    all c : Course | some teaches.c
}

pred  mult2 {
    all p : Project | some worksOn.p
}

pred mult3 {
    all p : Project | one proposes.p
}

pred mult4 { 
    all s : Student, c : Course | lone s.(c.grades) //relações ternárias exemplos
}

fact {
    mult1
    mult2
    mult3
}

pred annot1 {
    all p : Person | (some p.enrolled) implies p in Student
}

pred annot2 {
    teaches in Professor -> Course
}

pred annot3 {
    all c : Course | all g : Grade | c.grades.g in enrolled.c
}

pred annot4a {
    all s : Student, pr : s.worksOn |
        proposes.pr in s.enrolled
}

pred annot4b {
    all s : Student, c : Course | lone (c.proposes & s.worksOn)
}

pred studentProjects {
    all p : Project | some s : Student | s->p in worksOn
}

check studentProjects { studentProjects } expect 1

run ProfessorProject {
    some Professor.worksOn
} expect 1

check equivStudentProject {
    (some p : Professor, r : Project | p->r in worksOn)
        iff
    (some Professor.worksOn)
} for 10 expect 0