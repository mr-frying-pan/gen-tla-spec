---- MODULE handle_cast_16 ----
EXTENDS Integers, TLC \* TLC for map_update
CONSTANTS Processes, NIL

LOCAL Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL
LOCAL GenServer == INSTANCE GenServer WITH Processes <- Processes, NIL <- NIL
LOCAL TTpl == INSTANCE Type WITH Name <- "tuple"
LOCAL Map == INSTANCE Map

name == "handle_cast_16"
lines == 1..3

----
\* def handle_cast({:PROPOSE, from, value}, rbc)
\* In this function expressions are moved around a lot but the functionality should be preserved.

LOCAL line1(proc) ==
    LET
        from == Process!arg(proc, 1)[2]
        value == Process!arg(proc, 1)[3]
        rbc == Process!arg(proc, 2)
        predicate == rbc.predicate
        broadcaster == rbc.broadcaster
    IN
        IF broadcaster /= from THEN
            \* return as if nothing done, as (PIN-VAR) rule states in Deividas thesis
            Process!return(proc, <<"NOREPLY", rbc>>)
        ELSE
            Process!call(proc, predicate, <<value>>)

LOCAL line2(proc) ==
    LET
        predicate_result == Process!return_value(proc)
        rbc == Process!arg(proc, 2)
        echo_sent == rbc.echo_sent
        peers == rbc.peers
        me == rbc.me
        value == Process!arg(proc, 1)[3]
    IN
        IF ~echo_sent /\ predicate_result THEN
            GenServer!abcast(proc, peers, <<"ECHO", me, value>>)
        ELSE
            Process!return(proc, <<"NOREPLY", rbc>>)

LOCAL line3(proc) ==
    LET
        from == Process!arg(proc, 1)[2]
        rbc == Process!arg(proc, 2)
        msg_recv == rbc.msg_recv
        msg_recv_updated == Map!put(msg_recv, TTpl!c(<<from, "PROPOSE">>), TRUE)
        rbc_updated == [rbc EXCEPT !.echo_sent = TRUE, !.msg_recv = msg_recv_updated]
    IN
        Process!return(proc, <<"NOREPLY", rbc_updated>>)

----

line_enabled(proc, line) ==
    Process!line_enabled(proc, lines, name, line)

line_action(proc, line) ==
    CASE line = 1 -> line1(proc)
      [] line = 2 -> line2(proc)
      [] line = 3 -> line3(proc)
      [] OTHER    -> Process!error_pc

====