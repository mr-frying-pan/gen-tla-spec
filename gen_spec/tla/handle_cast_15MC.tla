---- MODULE handle_cast_15MC ----
EXTENDS TLC, FiniteSets, Integers
CONSTANT Processes

VARIABLES p, s, mq, nId, case
vars == <<p, s, mq, nId, case>>

this == CHOOSE x \in Processes: TRUE

LOCAL Process == INSTANCE Process WITH Processes <- Processes
LOCAL Messaging == INSTANCE Messaging WITH nextMsgId <- nId

LOCAL handle_cast_15 == INSTANCE handle_cast_15 WITH Processes <- Processes

fn_line(line_enabled, line_result) ==
    LET
        becomes_blocked == Process!blocked(line_result)
        complete_messages == Messaging!full_msgs(line_result.sent_msgs)
    IN
        /\  line_enabled
        /\  p' = line_result
        /\  mq' = Messaging!bulk_send(mq, complete_messages)
        /\  nId' = nId + Cardinality(complete_messages)
        /\  IF becomes_blocked THEN
                s' = [s EXCEPT !.wait_replies_for = complete_messages]
            ELSE
                UNCHANGED s

Termination ==
    /\ Process!terminated(p)
    /\ UNCHANGED vars

----

test_cases == {
        [msg |-> <<"INPUT", 10>>, state |-> [
            me |-> this,
            broadcaster |-> this,
            peers |-> Processes,
            propose_sent |-> FALSE
        ]],
        [msg |-> <<"INPUT", 19>>, state |-> [
            me |-> this,
            broadcaster |-> this,
            peers |-> Processes,
            propose_sent |-> FALSE
        ]]
    }

----

Init ==
    \E c \in test_cases:
        /\ case = c
        /\ p = Process!init_call(this, "handle_cast_15", <<c.msg, c.state>>)
        /\ s = [
                state |-> {},
                processing_message |-> Messaging!dummy_msg, \* dummy of the same type, is replaced with actual on the first message receive
                wait_replies_to |-> {}, \* set of messages process is waiting a reply to
                arrived |-> {}
            ]
        /\ mq = {}
        /\ nId = 1

Next ==
    /\ UNCHANGED case
    /\  \/ \E l \in handle_cast_15!lines:
            LET
                line_enabled == handle_cast_15!line_enabled(p, l)
                line_result  == handle_cast_15!line_action(p, l)
            IN
                fn_line(line_enabled, line_result)
        \/ Termination


Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

CorrectMsgs == Process!terminated(p) =>
    /\ Cardinality(mq) = Cardinality(Processes) \* correct amount of msgs
    /\ \A o \in Processes: \E m \in mq:
        /\ m.from = this
        /\ m.to = o
        /\ m.msg = <<"PROPOSE", this, case.msg[2]>>

CorrectReturn == Process!terminated(p) =>
    LET
        reply_type == p.return_value[1]
        state == p.return_value[2]
    IN
        /\ reply_type = "NOREPLY"
        /\ state.propose_sent = TRUE
        /\ state.me = case.state.me
        /\ state.broadcaster = case.state.broadcaster
        /\ state.peers = case.state.peers
====