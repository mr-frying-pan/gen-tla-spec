---- MODULE GenServer ----
EXTENDS TLC
CONSTANTS Processes, NIL

LOCAL Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL

mk_req(f, t, message) ==
    [from |-> f, to |-> t, msg |-> message]

cast(proc, to, msg) == [proc EXCEPT
    !.pc = Process!inc_pc(@),
    !.sent_msgs = @ \cup {mk_req(proc.self, to, msg)}
]

\* for now ignoring process groups and all that jazz
abcast(proc, others, msg) == [proc EXCEPT
    !.pc = Process!inc_pc(@),
    !.sent_msgs = @ \cup
        \* Print("DBG GenServer.abcast",
        {mk_req(proc.self, p, msg) : p \in others}
        \* )
]

call(proc, to, msg) == [Process!block(proc) EXCEPT
    !.sent_msgs = @ \cup
        \* Print("DBG GenServer.call",
        {mk_req(proc.self, to, msg)}
        \* )
]

multicall(proc, others, msg) == [Process!block(proc) EXCEPT
    !.sent_msgs = @ \cup
        \* Print("DBG GenServer",
        {mk_req(proc.self, p, msg) : p \in others}
        \* )
]

====