-------------------------- MODULE ConsistencyProof --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT N, STOP, MINREADNUM, EPS
ASSUME N>=2 /\ MINREADNUM>0 /\ EPS>=0 /\ STOP <=4
Nodes == 1..N  \*id of node
WriteUpdator == N+1
ReadUpdator == N+2
GlobalInit == N+3


(*
--algorithm vcchain
{
    variable MinReadNum=MINREADNUM,
            Epsilon=EPS,
            Stop=STOP,
            alive=[n \in Nodes |-> TRUE],\*node status
            msg = [ j \in Nodes |-> <<>> ],\*each node has a message box that receives message from other nodes
            vc=[ n \in Nodes |-> [ lc |-> <<>>, pt |-> 0 ] ],           
            v= <<>>;\*v[i] denotes the data version of node i           
            chain= <<>>;           
            lvc=FALSE;
            rvc=FALSE;
            lLock=FALSE;
            rLock=FALSE;
            w_on=TRUE;
            r_on=TRUE;
            lock=FALSE;
            chainLock=FALSE;
            
            
            
    define
    {IsAlive(e) == alive[e]
    AliveNodes == {n \in Nodes : alive[n]=TRUE}
    \*GetNext(s) == chain[s]\*return the successor of s in chain
    
    \*values in chain are the successor of the index, if no element equals s then no index's successor is s, s is not in the chain.
    \*InChain(s,front) == IF front=0 THEN FALSE ELSE IF s=front THEN TRUE ELSE IF InChain(s,chain[front]) THEN TRUE ELSE FALSE
    
    InChain(s) == ~(chain \in Seq(Nodes \ {s})) \*s is the node's id, is s in the chain? function Seq(S) donates a set of all subsequences of S.
    
    ChainNodes == {n \in Nodes: InChain(n)=TRUE} \* get the sequence of node id in the chain
    SelectAliveNode == CHOOSE n \in Nodes : alive[n]=TRUE
    \*SelectAliveNode == CHOOSE i \in AliveNodes: ~InChain(i) \*select an alive node not in the chain
    \*GetVersion(i) == v[chain[i]]\*i is the index in chain,return the version
    }          


    procedure compare(local,remote)\*local:local vectorclock, remote:vectorclock in the message, paramater lvc and rvc is the result computed by the procedure
    variable count = 1;
    {
    CR: lLock:= TRUE;
        rLock:= TRUE;
    VCC:while(count <= N){
            if(local[count] < remote[count]){
                rvc:=TRUE;
            }
            else if(local[count]>remote[count]){
                lvc:=TRUE;
            };
                                       
            if(count>=2 /\ lvc /\ rvc){\* local || remote
            CR0:return
            };
            CI: count:=count+1;
        };
        
    CR1: return
    }

    
    procedure sort(read)
    variable count1= 1,
            count2= 1,
            pre= <<>>,
            p= <<>>,           
    {
    S0: while(count1 < Len(read)){
            
            count2:= 1;
            
            
        S1: while(count2 <= Len(read) - count1){
                pre:= read[count2];
                p:= read[count2+1];
                
                await(~lLock /\ ~rLock);
                call compare(pre.mvc.lc,p.mvc.lc);
                
\*            S2: print "after compare:";
\*                print lvc;
\*                print rvc;
                
              S2: if(lvc /\ rvc){
\*                    if(v[pre.source] > v[p.source]){\*pre is bigger
\*                        read[count2] := p;
\*                    S3: read[count2+1] := pre;
\*                    }
\*                    else if(v[pre.source] = v[p.source]){
\*                        
\*                    }
                    
                    if(pre.mvc.pt + Epsilon > p.mvc.pt){\*pre is bigger
                        read[count2] := p;
                    S4: read[count2+1] := pre;  
                                 
                    };
                    
                }
                else if(lvc /\ ~rvc){\*pre is bigger
                    read[count2] := p;
                S5: read[count2+1] := pre;
                    
                };

            S6: lvc:=FALSE;
                rvc:=FALSE;
                lLock:= FALSE;
                rLock:= FALSE;
                count2:= count2+1;
            };
            
            \* when the inner loop ends, read[Len(read)-count1+1] is sorted
            
            chain := Append(chain, read[Len(read)-count1+1].source);
            
            count1:= count1+1;
        }; 
        
        chain:= Append(chain,read[1].source);                       
        return;
    }


    fair process(n \in Nodes)
    variable count= 1,
            readSet= {},
            read= <<>>,
            cmsg= <<>>,
            local= <<>>,
            remote= <<>>;
            
    {
\*    C0: if(Len(vc[self].lc)# N){
\*        C1: while(Len(vc[self].lc) <= N){\*initially each node's lc is consist of 0
\*                vc[self].lc:= vc[self].lc \o <<0>>;                
\*            }
\*        };
        
    C2: readSet:= {self};
        await(Len(vc[self].lc) = N);
        \*read:= <<[mvc |-> vc[self], source |-> self, type |-> 3]>>;
        await(Len(v) = N);
    C3: while(w_on \/ r_on){
        C4: await((msg[self]# <<>> /\ IsAlive(self)) \/ (~w_on /\ ~r_on));\* message is not null and node is alived
        C0: if(~w_on /\ ~r_on){
                goto C3;
            };
        C5: cmsg:= msg[self];
            
        C6: if(cmsg.type=0){\*write message
                await(Len(vc[self].lc) = N);
                local:= vc[self].lc;
                remote:= cmsg.mvc.lc;
                                          
                await(~lLock /\ ~rLock);
                call compare(local,remote);\*call the compare procedure
                           
                
            C7: if(lvc /\ ~rvc){\*remote -> local
                    
                    v[cmsg.source]:= v[self]; 
                    if(v[self] > Stop){
                        w_on:= FALSE;
                        r_on:= FALSE;
                    };                  
                    
                }
                else if(~lvc /\ rvc){\*local -> remote
                    vc[self]:= cmsg.mvc;
                    v[self]:= v[cmsg.source];
                    if(v[cmsg.source] > Stop){
                        w_on:= FALSE;
                        r_on:= FALSE;
                    };  
                }
                else if(lvc /\ rvc){\*local || remote
                
                    \*merge local and remote
                C1: while(count <= Len(vc[self].lc)){
                        if(vc[self].lc[count] < cmsg.mvc.lc[count]){
                            vc[self].lc[count]:= cmsg.mvc.lc[count];
                        }
                        else{
                            cmsg.mvc.lc[count]:= vc[self].lc[count];
                        };
                        count:= count + 1;
                    };
                    
                    count:=1; 
                
                    if(vc[self].pt+Epsilon < cmsg.mvc.pt){\*local -> remote
                            
                            
                            \*vc[self]:= cmsg.mvc;
                            v[self]:= v[cmsg.source];
                            if(v[cmsg.source] > Stop){
                                w_on:= FALSE;
                                r_on:= FALSE;
                            };  
                    }
                    else{\*remote -> local
                            
                            v[cmsg.source]:= v[self];
                            if(v[self] > Stop){
                                w_on:= FALSE;
                                r_on:= FALSE;
                            };                               
                            
                    };
                    
                    
                }
                else{\*local = remote
                    if(v[cmsg.source] < v[self]){
                        v[cmsg.source]:= v[self];
                    }
                    else if(v[cmsg.source] > v[self]){
                        v[self]:= v[cmsg.source];
                    };
                    
                    if(v[self] > Stop){
                        w_on:= FALSE;
                        r_on:= FALSE;
                    };  
                };
                
                               
\*                local:= <<>>;
\*                remote:= <<>>;
            C9: lvc:=FALSE;
                rvc:=FALSE;
                lLock:= FALSE;
                rLock:= FALSE;
                
            }
            else if(cmsg.type=1){\*read message
                \*await(msg[cmsg.source] = <<>> );
                msg[cmsg.source]:= [mvc |-> vc[self], source |-> self, type |-> 3];              
            }
            \*else if(cmsg.type=2){\*write response
                
            \*}
            else if(cmsg.type=3){\*read response
               if(Cardinality(readSet) <= MinReadNum){
                  if(cmsg.source \notin readSet){
                    read:= read \o <<cmsg>>;
                    readSet:= readSet \union {cmsg.source};
                  };
               }
               else{  
                  
                  if(Len(read) >= 1){
                    await(~lock); 
                    chainLock:=TRUE;
                    read:= Append(read,[mvc |-> vc[self], source |-> self, type |-> 3]);              
                    call sort(read);
                  
                 C8:w_on:=FALSE;
                    r_on:=FALSE;
                    read:= <<>>;
                    chain:= <<>>;
                    chainLock:=FALSE;
                  };
                  
                                   
               }
                             
            };
            
        C:  cmsg:= <<>>;
            msg[self]:= <<>> ;
        }    
    
    }


    fair process (w=WriteUpdator) 
    variable currentNode=0,count=1;        
    {
    P0: await(Len(v)=N);
    
    P3: while (w_on){
            
            currentNode:= SelectAliveNode;
            if(Len(vc[currentNode].lc)# N){
            P4: await(Len(vc[currentNode].lc)= N);
            };
            
        P5: if(v[currentNode] > Stop){
                w_on:= FALSE;
            }
            else{
                await(~chainLock);
                
                vc[currentNode].pt:=vc[currentNode].pt+1;
                lock:= TRUE;
                
            P6: 
                vc[currentNode].lc[currentNode]:= vc[currentNode].lc[currentNode]+1;               
                v[currentNode]:= v[currentNode]+1;
                lock:=FALSE;
                
            P7: while(count <= N){\* send message to other nodes
                    if(count#currentNode){
                        \*await(msg[count]= <<>> );
                        msg[count]:= [mvc |-> vc[currentNode], source |-> currentNode, type |-> 0];\*source means the id of the node that sends this message and type=0 means it's a write message
                    };
                    count:=count+1;
                };
                         
                count:=1;
            }
       }
    }  


   fair process (r=ReadUpdator)
   variable nowNode=0,count=1;
   {
   Q0: await(Len(v)=N);
   
   Q1: while(r_on){
           
           
           nowNode:= SelectAliveNode;
           if(v[nowNode] > Stop){
              r_on:= FALSE;
           }
           else{
               
           Q2: while(count <= N){
                   if(count#currentNode){
                        \*await(msg[count]= <<>> );
                        msg[count]:= [mvc |-> <<>>,source |-> nowNode, type |-> 1];
                    };
                    count:=count+1;
               };
               
               count:= 1;
           }
       }
   }
   
   
   
   fair process(i=GlobalInit)
   variable count=1;
   {
       I0:while(count<=N){
             v:= Append(v,0);
             \*vc[count].pt := GetNum;
             
         I1: while(Len(vc[count].lc) < N){
                vc[count].lc:= vc[count].lc \o <<0>>;
             };
             vc[count].lc[count]:= 1;
             
             count:=count+1;
          }
          
\*         while(w_on \/ r_on){
\*            n:=SelectAliveNode;
\*            vc[n].pt:=vc[n].pt+1;
\*         }
  
   }   
   
   
   
   
}



*)
\* BEGIN TRANSLATION (chksum(pcal) = "5103b717" /\ chksum(tla) = "a1c7c61b")
\* Process variable count of process n at line 137 col 14 changed to count_
\* Process variable read of process n at line 139 col 13 changed to read_
\* Process variable local of process n at line 141 col 13 changed to local_
\* Process variable remote of process n at line 142 col 13 changed to remote_
\* Process variable count of process w at line 290 col 28 changed to count_w
\* Process variable count of process r at line 330 col 23 changed to count_r
\* Process variable count of process i at line 359 col 13 changed to count_i
CONSTANT defaultInitValue
VARIABLES MinReadNum, Epsilon, Stop, alive, msg, vc, v, chain, lvc, rvc, 
          lLock, rLock, w_on, r_on, lock, chainLock, pc, stack

(* define statement *)
 IsAlive(e) == alive[e]
AliveNodes == {n \in Nodes : alive[n]=TRUE}





InChain(s) == ~(chain \in Seq(Nodes \ {s}))

ChainNodes == {n \in Nodes: InChain(n)=TRUE}
SelectAliveNode == CHOOSE n \in Nodes : alive[n]=TRUE

VARIABLES local, remote, count, read, count1, count2, pre, p, count_, readSet, 
          read_, cmsg, local_, remote_, currentNode, count_w, nowNode, 
          count_r, count_i

vars == << MinReadNum, Epsilon, Stop, alive, msg, vc, v, chain, lvc, rvc, 
           lLock, rLock, w_on, r_on, lock, chainLock, pc, stack, local, 
           remote, count, read, count1, count2, pre, p, count_, readSet, 
           read_, cmsg, local_, remote_, currentNode, count_w, nowNode, 
           count_r, count_i >>

ProcSet == (Nodes) \cup {WriteUpdator} \cup {ReadUpdator} \cup {GlobalInit}

Init == (* Global variables *)
        /\ MinReadNum = MINREADNUM
        /\ Epsilon = EPS
        /\ Stop = STOP
        /\ alive = [n \in Nodes |-> TRUE]
        /\ msg = [ j \in Nodes |-> <<>> ]
        /\ vc = [ n \in Nodes |-> [ lc |-> <<>>, pt |-> 0 ] ]
        /\ v = <<>>
        /\ chain = <<>>
        /\ lvc = FALSE
        /\ rvc = FALSE
        /\ lLock = FALSE
        /\ rLock = FALSE
        /\ w_on = TRUE
        /\ r_on = TRUE
        /\ lock = FALSE
        /\ chainLock = FALSE
        (* Procedure compare *)
        /\ local = [ self \in ProcSet |-> defaultInitValue]
        /\ remote = [ self \in ProcSet |-> defaultInitValue]
        /\ count = [ self \in ProcSet |-> 1]
        (* Procedure sort *)
        /\ read = [ self \in ProcSet |-> defaultInitValue]
        /\ count1 = [ self \in ProcSet |-> 1]
        /\ count2 = [ self \in ProcSet |-> 1]
        /\ pre = [ self \in ProcSet |-> <<>>]
        /\ p = [ self \in ProcSet |-> <<>>]
        (* Process n *)
        /\ count_ = [self \in Nodes |-> 1]
        /\ readSet = [self \in Nodes |-> {}]
        /\ read_ = [self \in Nodes |-> <<>>]
        /\ cmsg = [self \in Nodes |-> <<>>]
        /\ local_ = [self \in Nodes |-> <<>>]
        /\ remote_ = [self \in Nodes |-> <<>>]
        (* Process w *)
        /\ currentNode = 0
        /\ count_w = 1
        (* Process r *)
        /\ nowNode = 0
        /\ count_r = 1
        (* Process i *)
        /\ count_i = 1
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Nodes -> "C2"
                                        [] self = WriteUpdator -> "P0"
                                        [] self = ReadUpdator -> "Q0"
                                        [] self = GlobalInit -> "I0"]

CR(self) == /\ pc[self] = "CR"
            /\ lLock' = TRUE
            /\ rLock' = TRUE
            /\ pc' = [pc EXCEPT ![self] = "VCC"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, w_on, r_on, lock, chainLock, 
                            stack, local, remote, count, read, count1, count2, 
                            pre, p, count_, readSet, read_, cmsg, local_, 
                            remote_, currentNode, count_w, nowNode, count_r, 
                            count_i >>

VCC(self) == /\ pc[self] = "VCC"
             /\ IF count[self] <= N
                   THEN /\ IF local[self][count[self]] < remote[self][count[self]]
                              THEN /\ rvc' = TRUE
                                   /\ lvc' = lvc
                              ELSE /\ IF local[self][count[self]]>remote[self][count[self]]
                                         THEN /\ lvc' = TRUE
                                         ELSE /\ TRUE
                                              /\ lvc' = lvc
                                   /\ rvc' = rvc
                        /\ IF count[self]>=2 /\ lvc' /\ rvc'
                              THEN /\ pc' = [pc EXCEPT ![self] = "CR0"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "CI"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "CR1"]
                        /\ UNCHANGED << lvc, rvc >>
             /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                             chain, lLock, rLock, w_on, r_on, lock, chainLock, 
                             stack, local, remote, count, read, count1, count2, 
                             pre, p, count_, readSet, read_, cmsg, local_, 
                             remote_, currentNode, count_w, nowNode, count_r, 
                             count_i >>

CI(self) == /\ pc[self] = "CI"
            /\ count' = [count EXCEPT ![self] = count[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "VCC"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, read, count1, 
                            count2, pre, p, count_, readSet, read_, cmsg, 
                            local_, remote_, currentNode, count_w, nowNode, 
                            count_r, count_i >>

CR0(self) == /\ pc[self] = "CR0"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ count' = [count EXCEPT ![self] = Head(stack[self]).count]
             /\ local' = [local EXCEPT ![self] = Head(stack[self]).local]
             /\ remote' = [remote EXCEPT ![self] = Head(stack[self]).remote]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                             chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                             chainLock, read, count1, count2, pre, p, count_, 
                             readSet, read_, cmsg, local_, remote_, 
                             currentNode, count_w, nowNode, count_r, count_i >>

CR1(self) == /\ pc[self] = "CR1"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ count' = [count EXCEPT ![self] = Head(stack[self]).count]
             /\ local' = [local EXCEPT ![self] = Head(stack[self]).local]
             /\ remote' = [remote EXCEPT ![self] = Head(stack[self]).remote]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                             chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                             chainLock, read, count1, count2, pre, p, count_, 
                             readSet, read_, cmsg, local_, remote_, 
                             currentNode, count_w, nowNode, count_r, count_i >>

compare(self) == CR(self) \/ VCC(self) \/ CI(self) \/ CR0(self)
                    \/ CR1(self)

S0(self) == /\ pc[self] = "S0"
            /\ IF count1[self] < Len(read[self])
                  THEN /\ count2' = [count2 EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "S1"]
                       /\ UNCHANGED << chain, stack, read, count1, pre, p >>
                  ELSE /\ chain' = Append(chain,read[self][1].source)
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ count1' = [count1 EXCEPT ![self] = Head(stack[self]).count1]
                       /\ count2' = [count2 EXCEPT ![self] = Head(stack[self]).count2]
                       /\ pre' = [pre EXCEPT ![self] = Head(stack[self]).pre]
                       /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
                       /\ read' = [read EXCEPT ![self] = Head(stack[self]).read]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, lvc, 
                            rvc, lLock, rLock, w_on, r_on, lock, chainLock, 
                            local, remote, count, count_, readSet, read_, cmsg, 
                            local_, remote_, currentNode, count_w, nowNode, 
                            count_r, count_i >>

S1(self) == /\ pc[self] = "S1"
            /\ IF count2[self] <= Len(read[self]) - count1[self]
                  THEN /\ pre' = [pre EXCEPT ![self] = read[self][count2[self]]]
                       /\ p' = [p EXCEPT ![self] = read[self][count2[self]+1]]
                       /\ (~lLock /\ ~rLock)
                       /\ /\ local' = [local EXCEPT ![self] = pre'[self].mvc.lc]
                          /\ remote' = [remote EXCEPT ![self] = p'[self].mvc.lc]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "compare",
                                                                   pc        |->  "S2",
                                                                   count     |->  count[self],
                                                                   local     |->  local[self],
                                                                   remote    |->  remote[self] ] >>
                                                               \o stack[self]]
                       /\ count' = [count EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "CR"]
                       /\ UNCHANGED << chain, count1 >>
                  ELSE /\ chain' = Append(chain, read[self][Len(read[self])-count1[self]+1].source)
                       /\ count1' = [count1 EXCEPT ![self] = count1[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "S0"]
                       /\ UNCHANGED << stack, local, remote, count, pre, p >>
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, lvc, 
                            rvc, lLock, rLock, w_on, r_on, lock, chainLock, 
                            read, count2, count_, readSet, read_, cmsg, local_, 
                            remote_, currentNode, count_w, nowNode, count_r, 
                            count_i >>

S2(self) == /\ pc[self] = "S2"
            /\ IF lvc /\ rvc
                  THEN /\ IF pre[self].mvc.pt + Epsilon > p[self].mvc.pt
                             THEN /\ read' = [read EXCEPT ![self][count2[self]] = p[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "S4"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "S6"]
                                  /\ read' = read
                  ELSE /\ IF lvc /\ ~rvc
                             THEN /\ read' = [read EXCEPT ![self][count2[self]] = p[self]]
                                  /\ pc' = [pc EXCEPT ![self] = "S5"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "S6"]
                                  /\ read' = read
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, count, count1, 
                            count2, pre, p, count_, readSet, read_, cmsg, 
                            local_, remote_, currentNode, count_w, nowNode, 
                            count_r, count_i >>

S4(self) == /\ pc[self] = "S4"
            /\ read' = [read EXCEPT ![self][count2[self]+1] = pre[self]]
            /\ pc' = [pc EXCEPT ![self] = "S6"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, count, count1, 
                            count2, pre, p, count_, readSet, read_, cmsg, 
                            local_, remote_, currentNode, count_w, nowNode, 
                            count_r, count_i >>

S5(self) == /\ pc[self] = "S5"
            /\ read' = [read EXCEPT ![self][count2[self]+1] = pre[self]]
            /\ pc' = [pc EXCEPT ![self] = "S6"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, count, count1, 
                            count2, pre, p, count_, readSet, read_, cmsg, 
                            local_, remote_, currentNode, count_w, nowNode, 
                            count_r, count_i >>

S6(self) == /\ pc[self] = "S6"
            /\ lvc' = FALSE
            /\ rvc' = FALSE
            /\ lLock' = FALSE
            /\ rLock' = FALSE
            /\ count2' = [count2 EXCEPT ![self] = count2[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "S1"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, w_on, r_on, lock, chainLock, stack, local, 
                            remote, count, read, count1, pre, p, count_, 
                            readSet, read_, cmsg, local_, remote_, currentNode, 
                            count_w, nowNode, count_r, count_i >>

sort(self) == S0(self) \/ S1(self) \/ S2(self) \/ S4(self) \/ S5(self)
                 \/ S6(self)

C2(self) == /\ pc[self] = "C2"
            /\ readSet' = [readSet EXCEPT ![self] = {self}]
            /\ (Len(vc[self].lc) = N)
            /\ (Len(v) = N)
            /\ pc' = [pc EXCEPT ![self] = "C3"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, count, read, 
                            count1, count2, pre, p, count_, read_, cmsg, 
                            local_, remote_, currentNode, count_w, nowNode, 
                            count_r, count_i >>

C3(self) == /\ pc[self] = "C3"
            /\ IF w_on \/ r_on
                  THEN /\ pc' = [pc EXCEPT ![self] = "C4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, count, read, 
                            count1, count2, pre, p, count_, readSet, read_, 
                            cmsg, local_, remote_, currentNode, count_w, 
                            nowNode, count_r, count_i >>

C4(self) == /\ pc[self] = "C4"
            /\ ((msg[self]# <<>> /\ IsAlive(self)) \/ (~w_on /\ ~r_on))
            /\ pc' = [pc EXCEPT ![self] = "C0"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, count, read, 
                            count1, count2, pre, p, count_, readSet, read_, 
                            cmsg, local_, remote_, currentNode, count_w, 
                            nowNode, count_r, count_i >>

C0(self) == /\ pc[self] = "C0"
            /\ IF ~w_on /\ ~r_on
                  THEN /\ pc' = [pc EXCEPT ![self] = "C3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "C5"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, count, read, 
                            count1, count2, pre, p, count_, readSet, read_, 
                            cmsg, local_, remote_, currentNode, count_w, 
                            nowNode, count_r, count_i >>

C5(self) == /\ pc[self] = "C5"
            /\ cmsg' = [cmsg EXCEPT ![self] = msg[self]]
            /\ pc' = [pc EXCEPT ![self] = "C6"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, lvc, rvc, lLock, rLock, w_on, r_on, lock, 
                            chainLock, stack, local, remote, count, read, 
                            count1, count2, pre, p, count_, readSet, read_, 
                            local_, remote_, currentNode, count_w, nowNode, 
                            count_r, count_i >>

C6(self) == /\ pc[self] = "C6"
            /\ IF cmsg[self].type=0
                  THEN /\ (Len(vc[self].lc) = N)
                       /\ local_' = [local_ EXCEPT ![self] = vc[self].lc]
                       /\ remote_' = [remote_ EXCEPT ![self] = cmsg[self].mvc.lc]
                       /\ (~lLock /\ ~rLock)
                       /\ /\ local' = [local EXCEPT ![self] = local_'[self]]
                          /\ remote' = [remote EXCEPT ![self] = remote_'[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "compare",
                                                                   pc        |->  "C7",
                                                                   count     |->  count[self],
                                                                   local     |->  local[self],
                                                                   remote    |->  remote[self] ] >>
                                                               \o stack[self]]
                       /\ count' = [count EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "CR"]
                       /\ UNCHANGED << msg, chainLock, read, count1, count2, 
                                       pre, p, readSet, read_ >>
                  ELSE /\ IF cmsg[self].type=1
                             THEN /\ msg' = [msg EXCEPT ![cmsg[self].source] = [mvc |-> vc[self], source |-> self, type |-> 3]]
                                  /\ pc' = [pc EXCEPT ![self] = "C"]
                                  /\ UNCHANGED << chainLock, stack, read, 
                                                  count1, count2, pre, p, 
                                                  readSet, read_ >>
                             ELSE /\ IF cmsg[self].type=3
                                        THEN /\ IF Cardinality(readSet[self]) <= MinReadNum
                                                   THEN /\ IF cmsg[self].source \notin readSet[self]
                                                              THEN /\ read_' = [read_ EXCEPT ![self] = read_[self] \o <<cmsg[self]>>]
                                                                   /\ readSet' = [readSet EXCEPT ![self] = readSet[self] \union {cmsg[self].source}]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << readSet, 
                                                                                   read_ >>
                                                        /\ pc' = [pc EXCEPT ![self] = "C"]
                                                        /\ UNCHANGED << chainLock, 
                                                                        stack, 
                                                                        read, 
                                                                        count1, 
                                                                        count2, 
                                                                        pre, p >>
                                                   ELSE /\ IF Len(read_[self]) >= 1
                                                              THEN /\ (~lock)
                                                                   /\ chainLock' = TRUE
                                                                   /\ read_' = [read_ EXCEPT ![self] = Append(read_[self],[mvc |-> vc[self], source |-> self, type |-> 3])]
                                                                   /\ /\ read' = [read EXCEPT ![self] = read_'[self]]
                                                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "sort",
                                                                                                               pc        |->  "C8",
                                                                                                               count1    |->  count1[self],
                                                                                                               count2    |->  count2[self],
                                                                                                               pre       |->  pre[self],
                                                                                                               p         |->  p[self],
                                                                                                               read      |->  read[self] ] >>
                                                                                                           \o stack[self]]
                                                                   /\ count1' = [count1 EXCEPT ![self] = 1]
                                                                   /\ count2' = [count2 EXCEPT ![self] = 1]
                                                                   /\ pre' = [pre EXCEPT ![self] = <<>>]
                                                                   /\ p' = [p EXCEPT ![self] = <<>>]
                                                                   /\ pc' = [pc EXCEPT ![self] = "S0"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "C"]
                                                                   /\ UNCHANGED << chainLock, 
                                                                                   stack, 
                                                                                   read, 
                                                                                   count1, 
                                                                                   count2, 
                                                                                   pre, 
                                                                                   p, 
                                                                                   read_ >>
                                                        /\ UNCHANGED readSet
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "C"]
                                             /\ UNCHANGED << chainLock, stack, 
                                                             read, count1, 
                                                             count2, pre, p, 
                                                             readSet, read_ >>
                                  /\ msg' = msg
                       /\ UNCHANGED << local, remote, count, local_, remote_ >>
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, vc, v, chain, 
                            lvc, rvc, lLock, rLock, w_on, r_on, lock, count_, 
                            cmsg, currentNode, count_w, nowNode, count_r, 
                            count_i >>

C7(self) == /\ pc[self] = "C7"
            /\ IF lvc /\ ~rvc
                  THEN /\ v' = [v EXCEPT ![cmsg[self].source] = v[self]]
                       /\ IF v'[self] > Stop
                             THEN /\ w_on' = FALSE
                                  /\ r_on' = FALSE
                             ELSE /\ TRUE
                                  /\ UNCHANGED << w_on, r_on >>
                       /\ pc' = [pc EXCEPT ![self] = "C9"]
                       /\ vc' = vc
                  ELSE /\ IF ~lvc /\ rvc
                             THEN /\ vc' = [vc EXCEPT ![self] = cmsg[self].mvc]
                                  /\ v' = [v EXCEPT ![self] = v[cmsg[self].source]]
                                  /\ IF v'[cmsg[self].source] > Stop
                                        THEN /\ w_on' = FALSE
                                             /\ r_on' = FALSE
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << w_on, r_on >>
                                  /\ pc' = [pc EXCEPT ![self] = "C9"]
                             ELSE /\ IF lvc /\ rvc
                                        THEN /\ pc' = [pc EXCEPT ![self] = "C1"]
                                             /\ UNCHANGED << v, w_on, r_on >>
                                        ELSE /\ IF v[cmsg[self].source] < v[self]
                                                   THEN /\ v' = [v EXCEPT ![cmsg[self].source] = v[self]]
                                                   ELSE /\ IF v[cmsg[self].source] > v[self]
                                                              THEN /\ v' = [v EXCEPT ![self] = v[cmsg[self].source]]
                                                              ELSE /\ TRUE
                                                                   /\ v' = v
                                             /\ IF v'[self] > Stop
                                                   THEN /\ w_on' = FALSE
                                                        /\ r_on' = FALSE
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << w_on, 
                                                                        r_on >>
                                             /\ pc' = [pc EXCEPT ![self] = "C9"]
                                  /\ vc' = vc
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, chain, lvc, 
                            rvc, lLock, rLock, lock, chainLock, stack, local, 
                            remote, count, read, count1, count2, pre, p, 
                            count_, readSet, read_, cmsg, local_, remote_, 
                            currentNode, count_w, nowNode, count_r, count_i >>

C1(self) == /\ pc[self] = "C1"
            /\ IF count_[self] <= Len(vc[self].lc)
                  THEN /\ IF vc[self].lc[count_[self]] < cmsg[self].mvc.lc[count_[self]]
                             THEN /\ vc' = [vc EXCEPT ![self].lc[count_[self]] = cmsg[self].mvc.lc[count_[self]]]
                                  /\ cmsg' = cmsg
                             ELSE /\ cmsg' = [cmsg EXCEPT ![self].mvc.lc[count_[self]] = vc[self].lc[count_[self]]]
                                  /\ vc' = vc
                       /\ count_' = [count_ EXCEPT ![self] = count_[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "C1"]
                       /\ UNCHANGED << v, w_on, r_on >>
                  ELSE /\ count_' = [count_ EXCEPT ![self] = 1]
                       /\ IF vc[self].pt+Epsilon < cmsg[self].mvc.pt
                             THEN /\ v' = [v EXCEPT ![self] = v[cmsg[self].source]]
                                  /\ IF v'[cmsg[self].source] > Stop
                                        THEN /\ w_on' = FALSE
                                             /\ r_on' = FALSE
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << w_on, r_on >>
                             ELSE /\ v' = [v EXCEPT ![cmsg[self].source] = v[self]]
                                  /\ IF v'[self] > Stop
                                        THEN /\ w_on' = FALSE
                                             /\ r_on' = FALSE
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << w_on, r_on >>
                       /\ pc' = [pc EXCEPT ![self] = "C9"]
                       /\ UNCHANGED << vc, cmsg >>
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, chain, lvc, 
                            rvc, lLock, rLock, lock, chainLock, stack, local, 
                            remote, count, read, count1, count2, pre, p, 
                            readSet, read_, local_, remote_, currentNode, 
                            count_w, nowNode, count_r, count_i >>

C9(self) == /\ pc[self] = "C9"
            /\ lvc' = FALSE
            /\ rvc' = FALSE
            /\ lLock' = FALSE
            /\ rLock' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "C"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, 
                            chain, w_on, r_on, lock, chainLock, stack, local, 
                            remote, count, read, count1, count2, pre, p, 
                            count_, readSet, read_, cmsg, local_, remote_, 
                            currentNode, count_w, nowNode, count_r, count_i >>

C8(self) == /\ pc[self] = "C8"
            /\ w_on' = FALSE
            /\ r_on' = FALSE
            /\ read_' = [read_ EXCEPT ![self] = <<>>]
            /\ chain' = <<>>
            /\ chainLock' = FALSE
            /\ pc' = [pc EXCEPT ![self] = "C"]
            /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, lvc, 
                            rvc, lLock, rLock, lock, stack, local, remote, 
                            count, read, count1, count2, pre, p, count_, 
                            readSet, cmsg, local_, remote_, currentNode, 
                            count_w, nowNode, count_r, count_i >>

C(self) == /\ pc[self] = "C"
           /\ cmsg' = [cmsg EXCEPT ![self] = <<>>]
           /\ msg' = [msg EXCEPT ![self] = <<>>]
           /\ pc' = [pc EXCEPT ![self] = "C3"]
           /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, vc, v, chain, lvc, 
                           rvc, lLock, rLock, w_on, r_on, lock, chainLock, 
                           stack, local, remote, count, read, count1, count2, 
                           pre, p, count_, readSet, read_, local_, remote_, 
                           currentNode, count_w, nowNode, count_r, count_i >>

n(self) == C2(self) \/ C3(self) \/ C4(self) \/ C0(self) \/ C5(self)
              \/ C6(self) \/ C7(self) \/ C1(self) \/ C9(self) \/ C8(self)
              \/ C(self)

P0 == /\ pc[WriteUpdator] = "P0"
      /\ (Len(v)=N)
      /\ pc' = [pc EXCEPT ![WriteUpdator] = "P3"]
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, chain, lvc, 
                      rvc, lLock, rLock, w_on, r_on, lock, chainLock, stack, 
                      local, remote, count, read, count1, count2, pre, p, 
                      count_, readSet, read_, cmsg, local_, remote_, 
                      currentNode, count_w, nowNode, count_r, count_i >>

P3 == /\ pc[WriteUpdator] = "P3"
      /\ IF w_on
            THEN /\ currentNode' = SelectAliveNode
                 /\ IF Len(vc[currentNode'].lc)# N
                       THEN /\ pc' = [pc EXCEPT ![WriteUpdator] = "P4"]
                       ELSE /\ pc' = [pc EXCEPT ![WriteUpdator] = "P5"]
            ELSE /\ pc' = [pc EXCEPT ![WriteUpdator] = "Done"]
                 /\ UNCHANGED currentNode
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, chain, lvc, 
                      rvc, lLock, rLock, w_on, r_on, lock, chainLock, stack, 
                      local, remote, count, read, count1, count2, pre, p, 
                      count_, readSet, read_, cmsg, local_, remote_, count_w, 
                      nowNode, count_r, count_i >>

P5 == /\ pc[WriteUpdator] = "P5"
      /\ IF v[currentNode] > Stop
            THEN /\ w_on' = FALSE
                 /\ pc' = [pc EXCEPT ![WriteUpdator] = "P3"]
                 /\ UNCHANGED << vc, lock >>
            ELSE /\ (~chainLock)
                 /\ vc' = [vc EXCEPT ![currentNode].pt = vc[currentNode].pt+1]
                 /\ lock' = TRUE
                 /\ pc' = [pc EXCEPT ![WriteUpdator] = "P6"]
                 /\ w_on' = w_on
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, v, chain, lvc, 
                      rvc, lLock, rLock, r_on, chainLock, stack, local, remote, 
                      count, read, count1, count2, pre, p, count_, readSet, 
                      read_, cmsg, local_, remote_, currentNode, count_w, 
                      nowNode, count_r, count_i >>

P6 == /\ pc[WriteUpdator] = "P6"
      /\ vc' = [vc EXCEPT ![currentNode].lc[currentNode] = vc[currentNode].lc[currentNode]+1]
      /\ v' = [v EXCEPT ![currentNode] = v[currentNode]+1]
      /\ lock' = FALSE
      /\ pc' = [pc EXCEPT ![WriteUpdator] = "P7"]
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, chain, lvc, rvc, 
                      lLock, rLock, w_on, r_on, chainLock, stack, local, 
                      remote, count, read, count1, count2, pre, p, count_, 
                      readSet, read_, cmsg, local_, remote_, currentNode, 
                      count_w, nowNode, count_r, count_i >>

P7 == /\ pc[WriteUpdator] = "P7"
      /\ IF count_w <= N
            THEN /\ IF count_w#currentNode
                       THEN /\ msg' = [msg EXCEPT ![count_w] = [mvc |-> vc[currentNode], source |-> currentNode, type |-> 0]]
                       ELSE /\ TRUE
                            /\ msg' = msg
                 /\ count_w' = count_w+1
                 /\ pc' = [pc EXCEPT ![WriteUpdator] = "P7"]
            ELSE /\ count_w' = 1
                 /\ pc' = [pc EXCEPT ![WriteUpdator] = "P3"]
                 /\ msg' = msg
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, vc, v, chain, lvc, rvc, 
                      lLock, rLock, w_on, r_on, lock, chainLock, stack, local, 
                      remote, count, read, count1, count2, pre, p, count_, 
                      readSet, read_, cmsg, local_, remote_, currentNode, 
                      nowNode, count_r, count_i >>

P4 == /\ pc[WriteUpdator] = "P4"
      /\ (Len(vc[currentNode].lc)= N)
      /\ pc' = [pc EXCEPT ![WriteUpdator] = "P5"]
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, chain, lvc, 
                      rvc, lLock, rLock, w_on, r_on, lock, chainLock, stack, 
                      local, remote, count, read, count1, count2, pre, p, 
                      count_, readSet, read_, cmsg, local_, remote_, 
                      currentNode, count_w, nowNode, count_r, count_i >>

w == P0 \/ P3 \/ P5 \/ P6 \/ P7 \/ P4

Q0 == /\ pc[ReadUpdator] = "Q0"
      /\ (Len(v)=N)
      /\ pc' = [pc EXCEPT ![ReadUpdator] = "Q1"]
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, chain, lvc, 
                      rvc, lLock, rLock, w_on, r_on, lock, chainLock, stack, 
                      local, remote, count, read, count1, count2, pre, p, 
                      count_, readSet, read_, cmsg, local_, remote_, 
                      currentNode, count_w, nowNode, count_r, count_i >>

Q1 == /\ pc[ReadUpdator] = "Q1"
      /\ IF r_on
            THEN /\ nowNode' = SelectAliveNode
                 /\ IF v[nowNode'] > Stop
                       THEN /\ r_on' = FALSE
                            /\ pc' = [pc EXCEPT ![ReadUpdator] = "Q1"]
                       ELSE /\ pc' = [pc EXCEPT ![ReadUpdator] = "Q2"]
                            /\ r_on' = r_on
            ELSE /\ pc' = [pc EXCEPT ![ReadUpdator] = "Done"]
                 /\ UNCHANGED << r_on, nowNode >>
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, v, chain, lvc, 
                      rvc, lLock, rLock, w_on, lock, chainLock, stack, local, 
                      remote, count, read, count1, count2, pre, p, count_, 
                      readSet, read_, cmsg, local_, remote_, currentNode, 
                      count_w, count_r, count_i >>

Q2 == /\ pc[ReadUpdator] = "Q2"
      /\ IF count_r <= N
            THEN /\ IF count_r#currentNode
                       THEN /\ msg' = [msg EXCEPT ![count_r] = [mvc |-> <<>>,source |-> nowNode, type |-> 1]]
                       ELSE /\ TRUE
                            /\ msg' = msg
                 /\ count_r' = count_r+1
                 /\ pc' = [pc EXCEPT ![ReadUpdator] = "Q2"]
            ELSE /\ count_r' = 1
                 /\ pc' = [pc EXCEPT ![ReadUpdator] = "Q1"]
                 /\ msg' = msg
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, vc, v, chain, lvc, rvc, 
                      lLock, rLock, w_on, r_on, lock, chainLock, stack, local, 
                      remote, count, read, count1, count2, pre, p, count_, 
                      readSet, read_, cmsg, local_, remote_, currentNode, 
                      count_w, nowNode, count_i >>

r == Q0 \/ Q1 \/ Q2

I0 == /\ pc[GlobalInit] = "I0"
      /\ IF count_i<=N
            THEN /\ v' = Append(v,0)
                 /\ pc' = [pc EXCEPT ![GlobalInit] = "I1"]
            ELSE /\ pc' = [pc EXCEPT ![GlobalInit] = "Done"]
                 /\ v' = v
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, vc, chain, lvc, 
                      rvc, lLock, rLock, w_on, r_on, lock, chainLock, stack, 
                      local, remote, count, read, count1, count2, pre, p, 
                      count_, readSet, read_, cmsg, local_, remote_, 
                      currentNode, count_w, nowNode, count_r, count_i >>

I1 == /\ pc[GlobalInit] = "I1"
      /\ IF Len(vc[count_i].lc) < N
            THEN /\ vc' = [vc EXCEPT ![count_i].lc = vc[count_i].lc \o <<0>>]
                 /\ pc' = [pc EXCEPT ![GlobalInit] = "I1"]
                 /\ UNCHANGED count_i
            ELSE /\ vc' = [vc EXCEPT ![count_i].lc[count_i] = 1]
                 /\ count_i' = count_i+1
                 /\ pc' = [pc EXCEPT ![GlobalInit] = "I0"]
      /\ UNCHANGED << MinReadNum, Epsilon, Stop, alive, msg, v, chain, lvc, 
                      rvc, lLock, rLock, w_on, r_on, lock, chainLock, stack, 
                      local, remote, count, read, count1, count2, pre, p, 
                      count_, readSet, read_, cmsg, local_, remote_, 
                      currentNode, count_w, nowNode, count_r >>

i == I0 \/ I1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == w \/ r \/ i
           \/ (\E self \in ProcSet: compare(self) \/ sort(self))
           \/ (\E self \in Nodes: n(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self)) /\ WF_vars(compare(self)) /\ WF_vars(sort(self))
        /\ WF_vars(w)
        /\ WF_vars(r)
        /\ WF_vars(i)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 





Consistent == \A j,k \in Nodes : ( j<k /\ j<= Len(chain) /\ k<= Len(chain) ) => v[ chain[j] ] >= v[ chain[k] ]

\*Consistent == \A j,k \in Nodes : ( j<k /\ j<= Len(vars[8]) /\ k<= Len(vars[8]) ) => vars[7][ vars[8][j] ] >= vars[7][ vars[8][k] ]

\*Consistent == \A j,k \in Nodes :  j<k  => GetVersion(j) >= GetVersion(k)




=============================================================================
\* Modification History
\* Last modified Tue Aug 01 12:40:16 CST 2023 by 11051
\* Created Thu Jun 29 16:35:13 CST 2023 by 11051
