---- MODULE handle_cast_17 ----
EXTENDS Integers
CONSTANTS Processes, NIL

LOCAL Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL
LOCAL GenServer == INSTANCE GenServer WITH Processes <- Processes, NIL <- NIL
LOCAL TInt == INSTANCE Type WITH Name <- "int"
LOCAL TPid == INSTANCE Type WITH Name <- "pid"
LOCAL TTpl == INSTANCE Type WITH Name <- "tuple"
LOCAL Map == INSTANCE Map

name == "handle_cast_17"
lines == 1..4

----
\* def handle_cast({:ECHO, from, value}, rbc)

LOCAL line1(proc) ==
    LET
        from == Process!arg(proc, 1)[2]
        value == Process!arg(proc, 1)[3]
        rbc == Process!arg(proc, 2)
        echo_recv == rbc.echo_recv
        existing_recv == Map!get(echo_recv, TInt!c(value), Map!empty)
        value_recv == Map!put(existing_recv, TPid!c(from), TRUE)
    IN
        Process!bind(proc, "value_recv", value_recv)

LOCAL line2(proc) ==
    LET
        value == Process!arg(proc, 1)[3]
        rbc == Process!arg(proc, 2)
        value_recv == Process!val(proc, "value_recv")
        echo_recv == rbc.echo_recv
        echo_recv_updated == Map!put(echo_recv, TInt!c(value), value_recv)
        rbc_updated == [rbc EXCEPT !.echo_recv = echo_recv_updated]
    IN
        Process!bind(proc, "rbc", rbc_updated)

LOCAL line3(proc) ==
    LET
        value == Process!arg(proc, 1)[3]
        rbc == Process!val(proc, "rbc")
        value_recv == Process!val(proc, "value_recv")
        count == Map!size(value_recv)
        \* the rest are technically/in general incorrect, they should be taken from parameter
        \* but they were not previously modified, so they will be the same
        me == rbc.me
        n == rbc.n
        f == rbc.f
        peers == rbc.peers
        ready_sent == rbc.ready_sent

    IN
        IF ~ready_sent /\ count > ((n + f) \div 2) THEN
            GenServer!abcast(proc, peers, <<"READY", me, value>>)
        ELSE
            Process!return(proc, <<"NOREPLY", rbc>>)

LOCAL line4(proc) ==
    LET
        from == Process!arg(proc, 1)[2]
        rbc == Process!val(proc, "rbc")
        msg_recv == rbc.msg_recv \* technically incorrect but not modified previously
        msg_recv_updated == Map!put(msg_recv, TTpl!c(<<from, "ECHO">>), TRUE)
        rbc_updated == [rbc EXCEPT !.ready_sent = TRUE, !.msg_recv = msg_recv_updated]
    IN
        Process!return(proc, <<"NOREPLY", rbc_updated>>)

----

line_enabled(proc, line) ==
    Process!line_enabled(proc, lines, name, line)

line_action(proc, line) ==
    CASE line = 1 -> line1(proc)
      [] line = 2 -> line2(proc)
      [] line = 3 -> line3(proc)
      [] line = 4 -> line4(proc)
      [] OTHER    -> Process!error_pc
====