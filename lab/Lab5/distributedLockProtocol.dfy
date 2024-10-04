include "UtilitiesLibrary.dfy"

module Types {
  import opened UtilitiesLibrary

  type HostId = nat

  //Change this
  datatype Message =
    | None

  datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)
}


module ClientHost {
  import opened Types
  import opened UtilitiesLibrary

  //Add Constants
  datatype Constants = Constants()

  // What relationship must hold between this host's own constants and the
  // structure of the overall group of hosts? Change this for your constants.
  ghost predicate ConstantsValidForGroup(c: Constants, hostId:nat)
  {
    true
  }

  //Add variables
  datatype Variables = | Variables()
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    true
  }

  // Protocol steps. Define an action ghost predicate for each step of the protocol
  // that client can take in space below




  //Define Corresponding Next 
  datatype Step =

    | None

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
/*{*/
  case None => true
/*}*/
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}

module ServerHost {
  import opened Types
  import opened UtilitiesLibrary

  //Change this
  datatype Constants = Constants()

  // What relationship must hold between this host's own constants and the
  // structure of the overall group of hosts? Change this for your constants
  ghost predicate ConstantsValidForGroup(c: Constants, numHosts:nat)
  {
    true 
  }

  //Define this
  datatype Variables = | Variables()
  {
    ghost predicate WF(c: Constants) {
      true
    }
  }
  
  //define Init
  ghost predicate Init(c: Constants, v: Variables)
  {
    true
  }

  // Protocol steps. Define an action ghost predicate for each step of the protocol
  // that client can take.



  // Complete JayNF
  datatype Step =
    | None

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step, msgOps: MessageOps)
  {
    match step
/*{*/
  case None => true
/*}*/
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    exists step :: NextStep(c, v, v', step, msgOps)
  }
}

// We define a generic Host as able to be either of the specific roles.
// This is the ultimate (untrusted) definition of the protocol we're
// trying to verify.
// This definition is given to you to clarify how the two protocol roles above
// are pulled together into the ultimate distributed system.
module Host {
  import opened UtilitiesLibrary
  import opened Types
  import ClientHost
  import ServerHost

  datatype Constants =
    | ServerConstants(server: ServerHost.Constants)
    | ClientConstants(client: ClientHost.Constants)

  datatype Variables =
    | ServerVariables(server: ServerHost.Variables)
    | ClientVariables(client: ClientHost.Variables)
  {
    ghost predicate WF(c: Constants) {
      && (ClientVariables? <==> c.ClientConstants?)
      && (match c
            case ServerConstants(_) => server.WF(c.server)
            case ClientConstants(_) => client.WF(c.client)
          )
    }
  }

  // What property must be true of any group of hosts to run the protocol?
  // Generic DistributedSystem module calls back into this ghost predicate to ensure
  // that it has a well-formed *group* of hosts.

  ghost predicate GroupWFConstants(grp_c: seq<Constants>)
  {
    // There must at least be a server
    && 0 < |grp_c|
    // Last host is a server
    && Last(grp_c).ServerConstants?
    // All the others are clients
    && (forall hostid:nat | hostid < |grp_c| - 1 :: grp_c[hostid].ClientConstants?)
    // The server's constants must correctly account for the number of clients. 
    && ServerHost.ConstantsValidForGroup(Last(grp_c).server, |grp_c|-1)
    // The clients's constants must match their group positions.
    && (forall hostid:HostId | hostid < |grp_c| - 1
        :: ClientHost.ConstantsValidForGroup(grp_c[hostid].client, hostid))
  }

  ghost predicate GroupWF(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    && GroupWFConstants(grp_c)
    // Variables size matches group size defined by grp_c
    && |grp_v| == |grp_c|
    // Each host is well-formed
    && (forall hostid:HostId | hostid < |grp_c| :: grp_v[hostid].WF(grp_c[hostid]))
  }

  // Generic DistributedSystem module calls back into this ghost predicate to give
  // the protocol an opportunity to set up constraints across the various
  // hosts.  Protocol requires one server and the rest clients;
  // server must know how many clients, and clients must know
  // own ids.
  ghost predicate GroupInit(grp_c: seq<Constants>, grp_v: seq<Variables>)
  {
    // constants & variables are well-formed (same number of host slots as constants expect)
    && GroupWF(grp_c, grp_v)
    // server is initialized to know about the N-1 clients.
    // clients initted with their ids.
    && (ServerHost.Init(Last(grp_c).server, Last(grp_v).server))
    && (forall hostid:HostId | hostid < |grp_c| - 1 ::
        ClientHost.Init(grp_c[hostid].client, grp_v[hostid].client)
      )
  }

  // Dispatch Next to appropriate underlying implementation.
  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && (match c
      case ServerConstants(_) => ServerHost.Next(c.server, v.server, v'.server, msgOps)
      case ClientConstants(_) => ClientHost.Next(c.client, v.client, v'.client, msgOps)
      )
  }
}

// The (trusted) model of the environment: There is a network that can only deliver
// messages that some Host (running the protocol) has sent, but once sent, messages
// can be delivered repeatedly and in any order.
// This definition is given to you because it's a common assumption you can
// reuse. Someday you might decide to assume a different network model (e.g.
// reliable or at-most-once delivery), but this is a good place to start.
module Network {
  import opened Types

  datatype Constants = Constants  // no constants for network

  // Network state is the set of messages ever sent. Once sent, we'll
  // allow it to be delivered over and over.
  // (We don't have packet headers, so duplication, besides being realistic,
  // also doubles as how multiple parties can hear the message.)
  datatype Variables = Variables(sentMsgs:set<Message>)

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.sentMsgs == {}
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables, msgOps: MessageOps)
  {
    // Only allow receipt of a message if we've seen it has been sent.
    && (msgOps.recv.Some? ==> msgOps.recv.value in v.sentMsgs)
    // Record the sent message, if there was one.
    && (msgOps.send.Some? ==> v'.sentMsgs == v.sentMsgs + {msgOps.send.value})
    && (msgOps.send.None? ==> v'.sentMsgs == v.sentMsgs)
  }
}

// The (trusted) model of the distributed system: hosts don't share memory. Each
// takes its steps independently, interleaved in nondeterministic order with others.
// They only communicate through the network, and obey the communication model
// established by the Network model.
// This is given to you; it can be reused for just about any shared-nothing-concurrency
// protocol model.
module DistributedSystem {
  import opened UtilitiesLibrary
  import opened Types
  import Network
  import Host
  import ClientHost
  import ServerHost

  datatype Constants = Constants(
    hosts: seq<Host.Constants>,
    network: Network.Constants)
  {
    ghost predicate WF() {
      Host.GroupWFConstants(hosts)
    }
    ghost predicate ValidHostId(id: HostId) {
      id < |hosts|
    }
    ghost predicate ValidClientId(id: HostId){
      id < |hosts| - 1
    }
  }

  datatype Variables = Variables(
    hosts: seq<Host.Variables>,
    network: Network.Variables)
  {
    ghost predicate WF(c: Constants) {
      && c.WF()
      && Host.GroupWF(c.hosts, hosts)
    }
  }

  ghost predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && Host.GroupInit(c.hosts, v.hosts)
    && Network.Init(c.network, v.network)
  }

  ghost predicate HostAction(c: Constants, v: Variables, v': Variables, hostid: HostId, msgOps: MessageOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHostId(hostid)
    && Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], msgOps)
    // all other hosts UNCHANGED
    && (forall otherHost:nat | c.ValidHostId(otherHost) && otherHost != hostid :: v'.hosts[otherHost] == v.hosts[otherHost])
  }

  // JayNF is pretty simple as there's only a single action disjunct
  datatype Step =
    | HostActionStep(hostid: HostId, msgOps: MessageOps)

  ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    && HostAction(c, v, v', step.hostid, step.msgOps)
    // network agrees recv has been sent and records sent
    && Network.Next(c.network, v.network, v'.network, step.msgOps)
  }

  ghost predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }

  // Convince us that your model does something
  //uncomment last 2 lines, change variable names accordingly
  lemma PseudoLiveness(c: Constants) returns (behavior: seq<Variables>)
    requires c.WF()
    requires |c.hosts| == 2
    ensures 0 < |behavior|
    ensures Init(c, behavior[0])
    ensures forall i:nat | i < |behavior|-1 :: Next(c, behavior[i], behavior[i+1])
    ensures Last(behavior).WF(c)
    //ensures Last(behavior).hosts[1].server.lockOwner == 0
    //ensures Last(behavior).hosts[0].client.hasLock
  {
  }
}


