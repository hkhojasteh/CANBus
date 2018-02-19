module CANBus

/* Basic Model of Controller Area Network (CAN bus).
 * A Controller Area Network (CAN bus) is a vehicle bus standard designed to allow microcontrollers
 *      and devices to communicate with each other in applications without a host computer on subscriber bus.
 *      It is a message-based protocol, designed for multiplex electrical wiring within automobiles and other contexts.
 *      The devices that are connected by a CAN network are typically sensors, actuators, and other control devices.
 *
 *	Notes: Some ideas inspired by the  firewire, messaging, chord and farmer(ordering) examples.
 *
 * CAN is a multi-master serial bus standard for connecting Electronic Control Units [ECUs] also known as nodes.
 * Two or more nodes are required on the CAN network to communicate. Each node is able to send and receive me-
 * ssages, but not simultaneously. A message or Fr ame consists primarily of the ID (identifier), which represents the
 * priority of the message, and data bytes. The message is transmitted serially onto the bus and may be received
 * by all nodes.
 * 
 * author: Hadi Abdi Khojasteh
 * email: hkhojasteh [at] iasbs.ac.ir
 */

open util/ordering[TimeSlot] as ord

sig Node {}

sig MState {
	from: Node,											// Node that sent the message
	to: set Node										// Intended recipient(s) of a message
}

abstract sig Msg {
	state: MState,										// Timestamp: the TimeSlot on which the message was sent
	sentOn: TimeSlot,
	readOn: Node -> lone TimeSlot						// TimeSlot at which node reads message, if read
}{
	readOn.TimeSlot in state.to
}

/* CAN has four frame types:
 *      Data frame: a frame containing node data for transmission
 *      Remote frame: a frame requesting the transmission of a specific identifier
 *      Error frame: a frame transmitted by any node detecting an error
 *      Overload frame: a frame to inject a delay between data and/or remote frame
 */

sig Msg_Data, Msg_Remote, Msg_Error, Msg_Overload extends Msg {}

sig TimeSlot {
    // Typically, a node would determine the messages it sends and its next state, based on its current state and the messages it reads.
 	// The messages that the node actually reads are a subset of this set. Determined by constraints in this module.
	inChannel: Node -> Msg,

    // Messages that the node _actually reads_ in this TimeSlot must be inChannel before this read.
	read: Node -> Msg,

    // Messages sent by the node in this TimeSlot. They become inChannel (and can be read by) on the next TimeSlot.
	sent: Node -> Msg,

	// Messages available for sending at this TimeSlot.
	// A given message Messages available for sending at this TimeSlot. 
	available: set Msg,

   // Check having enough messages available for sending.
	needsToSend: Node -> Msg
}

fun MsgsSentOnTimeSlot[t: TimeSlot]: set Msg { t.sent[Node] }
fun MsgsReadOnTimeSlot[t: TimeSlot]: set Msg { t.read[Node] }

fact RulesOfCANBus {
	// Life cycle of message(Not always for TimeSlot):	available-> sent, inChannel-> read-> not inChannel
	// inChannel means it's ready for sending to channel but it can be send in next TimeSlot
	Msg in TimeSlot.sent[Node]							// all messages must be sent
	read in inChannel									// Read Only if messages is inChannel

	no ord/first.inChannel[Node]						// At the beginning, no messages have been sent yet

	// Messages sent on a given TimeSlot become inChannel on the subsequent TimeSlot.
	all pre: TimeSlot - ord/last | let post = ord/next[pre] | {
		// Messages sent on this TimeSlot are no longer available on subsequent TimeSlot
        post.available = pre.available - MsgsSentOnTimeSlot[pre]
     }

	all t: TimeSlot | {
		// Messages sent on a TimeSlot are taken from the pool of available (not-yet-sent) message atoms
		MsgsSentOnTimeSlot[t] in t.available

		// Timestamps are correct
		MsgsSentOnTimeSlot[t].sentOn in t
		MsgsReadOnTimeSlot[t].readOn[Node] in t

		// The only new message atoms are those sent by nodes
		MsgsSentOnTimeSlot[t] = t.sent[Node]

		all n: Node, m: Msg | m.readOn[n] = t => m in t.read[n]
		// Return addresses are correct
		all n: Node | t.sent[n].state.from in n

		// Messages sent to a node on a TimeSlot become inChannel on some subseqent TimeSlot,
		// and permanently stop being inChannel on the TimeSlot after that node reads the message
		all n: Node, m: Msg | {
			// Message starts being inChannel no earlier than it is sent;
			// Only messages sent to this node are inChannel.
			(m in t.inChannel[n] => (n in m.state.to && m.sentOn in ord/prevs[t]))
			// Message permanently stops being inChannel immediately after being read
			(m in t.read[n] => m !in ord/nexts[t].inChannel[n])
		}
	}
}
