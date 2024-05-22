---- MODULE TypeMC ----

T1 == INSTANCE Type WITH Name <- "t1"
T2 == INSTANCE Type WITH Name <- "t2"

v11 == T1!c(1)
v12 == T1!c(1)
v13 == T1!c(2)

v21 == T2!c("one")
v22 == T2!c("one")
v23 == T2!c("two")

Spec ==
    /\ v11 = v12
    /\ v11 # v13

    /\ v21 = v22
    /\ v21 # v23

    /\ v11 # v21
    \* /\ 1 # "one" \* uncomment this to see error
====