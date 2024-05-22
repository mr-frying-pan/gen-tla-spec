---- MODULE handle_cast_15 ----
EXTENDS Integers
CONSTANTS Processes, NIL

LOCAL Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL
LOCAL GenServer == INSTANCE GenServer WITH Processes <- Processes, NIL <- NIL

name == "handle_cast_15"
lines == 1..2

----
\* def handle_cast({:INPUT, input}, rbc)

LOCAL line1(proc) ==
    LET
        rbc == Process!arg(proc, 2)
        me == rbc.me
        broadcaster == rbc.broadcaster
        peers == rbc.peers
        propose_sent == rbc.propose_sent
        input == Process!arg(proc, 1)[2]
    IN
        IF broadcaster /= me \/ propose_sent /= FALSE THEN
            \* return as if nothing done, as (PIN-VAR) rule states in Deividas thesis
            Process!return(proc, <<"NOREPLY", rbc>>)
        ELSE
            \* Cannot also return here as return clears sent_msgs
            GenServer!abcast(proc, peers, <<"PROPOSE", me, input>>)

LOCAL line2(proc) ==
    LET
        rbc == Process!arg(proc, 2)
        \* Swapped rbc update with abcast, shouldn't impact anything.
        \* In general should come before, on separate line with variable assignment
        updated_rbc == [rbc EXCEPT !.propose_sent = TRUE]
    IN
        Process!return(proc, <<"NOREPLY", updated_rbc>>)

----

line_enabled(proc, line) ==
    Process!line_enabled(proc, lines, name, line)

line_action(proc, line) ==
    CASE line = 1 -> line1(proc)
      [] line = 2 -> line2(proc)
      [] OTHER    -> Process!error_pc
====