---- MODULE bracha ----
EXTENDS FiniteSets, Integers, TLC
CONSTANTS
    NIL,
    Processes,
    Clients,
    InitialMessages, \* should be of the form [from |-> client, to |-> process, msg |-> message]
    InitParams, \* what is passed into init function for every process, should be a function with domain Processes
    PreInitialAppState \* what is used as initial value for application state

VARIABLE procState
VARIABLE sysState
VARIABLE messageQueue \* all requests in transit

VARIABLE nextMsgId \* to keep track of which message is a reply to which, always increasing variable is defined

vars == <<procState, sysState, messageQueue, nextMsgId>>

LOCAL Process == INSTANCE Process WITH Processes <- Processes, NIL <- NIL
LOCAL Messaging == INSTANCE Messaging WITH Processes <- Processes \cup Clients, nextMsgId <- nextMsgId
LOCAL System == INSTANCE System WITH Processes <- Processes \cup Clients

\* function instances
\* manually added
LOCAL init == INSTANCE init WITH Processes <- Processes
LOCAL predicate == INSTANCE predicate WITH Processes <- Processes

\* auto generated
LOCAL handle_cast_15 == INSTANCE handle_cast_15 WITH Processes <- Processes
LOCAL handle_cast_16 == INSTANCE handle_cast_16 WITH Processes <- Processes
LOCAL handle_cast_17 == INSTANCE handle_cast_17 WITH Processes <- Processes
LOCAL handle_cast_18 == INSTANCE handle_cast_18 WITH Processes <- Processes

upd_proc_state(process, newState) == [procState EXCEPT ![process] = newState]
upd_sys_state(process, newState)  == [sysState EXCEPT ![process] = newState]

----
handler_handle_cast_15 ==
  \E t \in Processes, m \in messageQueue:
    /\ m.to = t
    /\ TRUE /\ m.msg[1] = "INPUT"
    /\ Process!waiting(procState[t]) \* process which has received the message is not currently processing any other
    /\ procState' = upd_proc_state(t, Process!call(Process!to_finished(procState[t]), handle_cast_15!name, <<m.msg, sysState[t].state>>))
    /\ messageQueue' = Messaging!drop(messageQueue, m)
    /\ sysState' = upd_sys_state(t, System!set_processing_message(sysState[t], m))
    /\ UNCHANGED nextMsgId


handler_handle_cast_16 ==
  \E t \in Processes, m \in messageQueue:
    /\ m.to = t
    /\ TRUE /\ m.msg[1] = "PROPOSE"
    /\ Process!waiting(procState[t]) \* process which has received the message is not currently processing any other
    /\ procState' = upd_proc_state(t, Process!call(Process!to_finished(procState[t]), handle_cast_16!name, <<m.msg, sysState[t].state>>))
    /\ messageQueue' = Messaging!drop(messageQueue, m)
    /\ sysState' = upd_sys_state(t, System!set_processing_message(sysState[t], m))
    /\ UNCHANGED nextMsgId


handler_handle_cast_17 ==
  \E t \in Processes, m \in messageQueue:
    /\ m.to = t
    /\ TRUE /\ m.msg[1] = "ECHO"
    /\ Process!waiting(procState[t]) \* process which has received the message is not currently processing any other
    /\ procState' = upd_proc_state(t, Process!call(Process!to_finished(procState[t]), handle_cast_17!name, <<m.msg, sysState[t].state>>))
    /\ messageQueue' = Messaging!drop(messageQueue, m)
    /\ sysState' = upd_sys_state(t, System!set_processing_message(sysState[t], m))
    /\ UNCHANGED nextMsgId


handler_handle_cast_18 ==
  \E t \in Processes, m \in messageQueue:
    /\ m.to = t
    /\ TRUE /\ m.msg[1] = "READY"
    /\ Process!waiting(procState[t]) \* process which has received the message is not currently processing any other
    /\ procState' = upd_proc_state(t, Process!call(Process!to_finished(procState[t]), handle_cast_18!name, <<m.msg, sysState[t].state>>))
    /\ messageQueue' = Messaging!drop(messageQueue, m)
    /\ sysState' = upd_sys_state(t, System!set_processing_message(sysState[t], m))
    /\ UNCHANGED nextMsgId

----
after_init ==
    \E p \in Processes:
        /\ Process!initialized(procState[p])
        /\ procState' = upd_proc_state(p, Process!return(procState[p], NIL))
        /\  LET
                init_ok == procState[p].return_value[1]
                init_value == procState[p].return_value[2]
            IN
                IF init_ok = "OK" THEN
                    sysState' = upd_sys_state(p, System!set_app_state(sysState[p], init_value))
                ELSE
                     \* if init returns something else just set {}, hope that something else breaks?
                    sysState' = upd_sys_state(p, System!set_app_state(sysState[p], {}))
        /\ UNCHANGED <<messageQueue, nextMsgId>>

handler_finished ==
    \E p \in Processes:
        /\ Process!finished(procState[p])
        /\ procState' = upd_proc_state(p, Process!return(procState[p], NIL))
        \* {:reply, resp, state} or {:noreply, state}
        /\  LET
                return_type == procState[p].return_value[1]
            IN
                CASE return_type = "REPLY" ->
                    /\ messageQueue' = Messaging!reply(messageQueue, procState[p].return_value[2], sysState[p].processing_message)
                    /\ sysState' = upd_sys_state(p, System!set_app_state(sysState[p], procState[p].return_value[3]))
                    /\ nextMsgId' = nextMsgId + 1 \* increment after sending reply
                  [] return_type = "NOREPLY" ->
                    /\ sysState' = upd_sys_state(p, System!set_app_state(sysState[p], procState[p].return_value[2]))
                    /\ UNCHANGED <<messageQueue, nextMsgId>>
                  [] OTHER -> UNCHANGED <<sysState, messageQueue, nextMsgId>> \* here probably should error happen

waiting_responses ==
    \E p \in Processes, m \in messageQueue:
        /\ Process!blocked(procState[p])
        /\ sysState[p].wait_replies_to /= {} \* not all responses received
        /\ m.to = p
        /\ \E w \in sysState[p].wait_replies_to:
            /\ m.reply_to = w.id \* m is a reply to one of the messages we are waiting a reply to
            \* do I need to check from?
            \* save as received to be delivered later
            /\ sysState' = upd_sys_state(p, System!received_response_for(sysState[p], w, m))
            /\ messageQueue' = Messaging!drop(messageQueue, m) \* remove from queue, got it already
            /\ UNCHANGED <<procState, nextMsgId>>

deliver_responses ==
    \E p \in Processes:
        /\ Process!blocked(procState[p]) \* still blocked
        /\ sysState[p].wait_replies_to = {} \* no replies to wait for
        /\ procState' = upd_proc_state(p, Process!return(procState[p], {<<resp.from, resp.msg>> : resp \in sysState[p].arrived})) \* return received msgs in multicall format
        /\ sysState' = upd_sys_state(p, System!clear_arrived(sysState[p])) \* clear arrived msgs, don't want them returned with the second call as well
        /\ UNCHANGED <<messageQueue, nextMsgId>>

fn_line(process, line_enabled, line_result) ==
    LET
        becomes_blocked == Process!blocked(line_result)
        complete_messages == Messaging!full_msgs(line_result.sent_msgs)
    IN
        /\  line_enabled
        \* /\  Print(<<process, "BEFORE", procState[process], sysState[process], "AFTER", line_result>>, TRUE)
        /\  procState' = upd_proc_state(process, line_result)
        /\  messageQueue' = Messaging!bulk_send(messageQueue, complete_messages)
        /\  nextMsgId' = nextMsgId + Cardinality(complete_messages)
        /\  IF becomes_blocked THEN
                sysState' = upd_sys_state(process, System!set_wait_replies_to(sysState[process], complete_messages))
            ELSE
                UNCHANGED sysState

function_lines ==
  /\ \E p \in Processes:
    \* manually added:
    \/ \E l \in init!lines:
        LET
            line_enabled == init!line_enabled(procState[p], l)
            line_result  == init!line_action(procState[p], l)
        IN
            fn_line(p, line_enabled, line_result)
    \/ \E l \in predicate!lines:
        LET
            line_enabled == predicate!line_enabled(procState[p], l)
            line_result  == predicate!line_action(procState[p], l)
        IN
            fn_line(p, line_enabled, line_result)
    \* automatically generated
    \/ \E l \in handle_cast_15!lines:
        LET
            line_enabled == handle_cast_15!line_enabled(procState[p], l)
            line_result  == handle_cast_15!line_action(procState[p], l)
        IN
            fn_line(p, line_enabled, line_result)
    \/ \E l \in handle_cast_16!lines:
        LET
            line_enabled == handle_cast_16!line_enabled(procState[p], l)
            line_result  == handle_cast_16!line_action(procState[p], l)
        IN
            fn_line(p, line_enabled, line_result)
    \/ \E l \in handle_cast_17!lines:
        LET
            line_enabled == handle_cast_17!line_enabled(procState[p], l)
            line_result  == handle_cast_17!line_action(procState[p], l)
        IN
            fn_line(p, line_enabled, line_result)
    \/ \E l \in handle_cast_18!lines:
        LET
            line_enabled == handle_cast_18!line_enabled(procState[p], l)
            line_result  == handle_cast_18!line_action(procState[p], l)
        IN
            fn_line(p, line_enabled, line_result)

----
\* to prevent deadlock, not sure this is needed
Termination ==
    \* all processes waiting
    /\ \A p \in Processes: Process!waiting(procState[p])
    \* no messages to handle
    /\ ~ENABLED handler_handle_cast_15
    /\ ~ENABLED handler_handle_cast_16
    /\ ~ENABLED handler_handle_cast_17
    /\ ~ENABLED handler_handle_cast_18
    /\ UNCHANGED vars

Init ==
    /\ procState = [p \in Processes |-> Process!init(p, "init", InitParams[p])]
    /\ sysState = [p \in Processes |-> System!init(PreInitialAppState)]
    /\ messageQueue = Messaging!init_msgs(InitialMessages)
    /\ nextMsgId = Cardinality(InitialMessages) + 1

Next ==
  \/ handler_handle_cast_15
  \/ handler_handle_cast_16
  \/ handler_handle_cast_17
  \/ handler_handle_cast_18
  \/ after_init
  \/ handler_finished
  \/ function_lines
  \/ waiting_responses
  \/ deliver_responses
  \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----
TypeOk ==
    LET
        fns == {
            init!name,
            predicate!name,
            handle_cast_15!name,
            handle_cast_16!name,
            handle_cast_17!name,
            handle_cast_18!name
        }
    IN
        /\ \A p \in Processes: Process!TypeOk(procState[p], fns)
        /\ \A p \in Processes: System!TypeOk(sysState[p])
        /\ messageQueue \in SUBSET Messaging!possible_msgs
        /\ nextMsgId \in Nat
====