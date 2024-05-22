---- MODULE handle_cast_16MC ----
EXTENDS TLC, FiniteSets, Integers
CONSTANT Processes

VARIABLES p, s, mq, nId, case
vars == <<p, s, mq, nId, case>>

this == CHOOSE x \in Processes: TRUE
other == CHOOSE o \in Processes: o /= this

LOCAL Process == INSTANCE Process WITH Processes <- Processes
LOCAL Messaging == INSTANCE Messaging WITH nextMsgId <- nId
LOCAL TTpl == INSTANCE Type WITH Name <- "tuple"
LOCAL Map == INSTANCE Map

LOCAL handle_cast_16 == INSTANCE handle_cast_16 WITH Processes <- Processes

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
        [ \* usual case, echo not sent before, send to all
            msg |-> <<"PROPOSE", this, 1>>,
            state |-> [
                me |-> this,
                broadcaster |-> this,
                peers |-> Processes,
                predicate |-> "predicate",
                echo_sent |-> FALSE,
                msg_recv |-> Map!empty
            ],
            expected_state |-> [
                me |-> this,
                broadcaster |-> this,
                peers |-> Processes,
                predicate |-> "predicate",
                echo_sent |-> TRUE,
                msg_recv |-> Map!put(Map!empty, TTpl!c(<<this, "PROPOSE">>), TRUE)
            ],
            expected_mq |-> {[from |-> this, to |-> o, msg |-> <<"ECHO", this, 1>>] : o \in Processes}
        ],
        [ \* wrong broadcaster, do not send again
            msg |-> <<"PROPOSE", this, 2>>,
            state |-> [
                me |-> this,
                broadcaster |-> other,
                peers |-> Processes,
                predicate |-> "predicate",
                echo_sent |-> FALSE,
                msg_recv |-> Map!empty
            ],
            expected_state |-> [
                me |-> this,
                broadcaster |-> other,
                peers |-> Processes,
                predicate |-> "predicate",
                echo_sent |-> FALSE,
                msg_recv |-> Map!empty
            ],
            expected_mq |-> {}
        ],
        [ \* echo sent before, do not send again
            msg |-> <<"PROPOSE", this, 3>>,
            state |-> [
                me |-> this,
                broadcaster |-> this,
                peers |-> Processes,
                predicate |-> "predicate",
                echo_sent |-> TRUE,
                msg_recv |-> Map!empty
            ],
            expected_state |-> [
                me |-> this,
                broadcaster |-> this,
                peers |-> Processes,
                predicate |-> "predicate",
                echo_sent |-> TRUE,
                msg_recv |-> Map!empty
            ],
            expected_mq |-> {}
        ]
    }

----

Init ==
    \E c \in test_cases:
        /\ case = c
        /\ p = Process!init_call(this, "handle_cast_16", <<c.msg, c.state>>)
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
    /\  \/ \E l \in handle_cast_16!lines:
            LET
                line_enabled == handle_cast_16!line_enabled(p, l)
                line_result  == handle_cast_16!line_action(p, l)
            IN
                fn_line(line_enabled, line_result)
        \/  /\ p.pc.fn = "predicate"
            /\ p' = Process!return(p, TRUE)
            /\ UNCHANGED <<mq, nId, s>>
        \/ Termination


Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----

CorrectMsgs == Process!terminated(p) =>
    /\ Cardinality(mq) = Cardinality(case.expected_mq) \* correct amount of msgs
    /\ \A em \in case.expected_mq: \E m \in mq:
        /\ m.from = em.from
        /\ m.to = em.to
        /\ m.msg = em.msg

CorrectReturn == Process!terminated(p) =>
    LET
        reply_type == p.return_value[1]
        state == p.return_value[2]
    IN
        /\ reply_type = "NOREPLY"
        /\ state = case.expected_state
====