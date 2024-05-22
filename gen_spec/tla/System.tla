---- MODULE System ----
EXTENDS TLC
CONSTANT Processes

LOCAL Messaging == INSTANCE Messaging WITH Processes <- Processes, nextMsgId <- 0 \* ids don't matter, won't be sending any messages

TypeOk(sys) ==
    /\ "state" \in DOMAIN sys
    /\ "processing_message" \in DOMAIN sys /\ sys.processing_message \in Messaging!possible_msgs
    /\ "wait_replies_to" \in DOMAIN sys /\ sys.wait_replies_to \in SUBSET Messaging!possible_msgs
    /\ "arrived" \in DOMAIN sys /\ sys.arrived \in SUBSET Messaging!possible_msgs

----

init(initial_state) == [
    state |-> initial_state,
    processing_message |-> Messaging!dummy_msg, \* message currently being processed. Will be replaced with actual on first receive
    wait_replies_to |-> {}, \* set of messages process is waiting a reply to
    arrived |-> {}          \* set of messages process has received as a reply
]

set_app_state(sys, newState) ==
    [sys EXCEPT !.state = newState]

set_processing_message(sys, processingMessage) ==
    [sys EXCEPT !.processing_message = processingMessage]

set_wait_replies_to(sys, newWaitRepliesTo) ==
    [sys EXCEPT !.wait_replies_to = newWaitRepliesTo]

received_response_for(sys, waiting, arrived) ==
    [sys EXCEPT !.wait_replies_to = @ \ {waiting}, !.arrived = @ \cup {arrived}]

clear_arrived(sys) ==
    [sys EXCEPT !.arrived = {}]

====