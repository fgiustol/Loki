from zksk import Secret, DLRep
from zksk.primitives.dl_notequal import DLNotEqual
from zksk.primitives.rangeproof import RangeStmt, RangeOnlyStmt, PowerTwoRangeStmt
import petlib.bn as bn
from elGamal import keygen, dec, enc, re_enc
import time
from functools import reduce

def setup():
    #Generation of public params and voting server key pair
    g, order, pk_vs, sk_vs = keygen()
    
    #Generation of Tallier key pair
    sk_T = order.random()
    pk_T = sk_T*g
    return g, order, pk_vs, sk_vs, sk_T, pk_T

def stmt(public_params, private_params, candidates):
    """Constructs the statement for the ZK proofs in Vote and Obfuscate

    Args: 
        public_params (tuple): public parameters
        private_params (tuple): private parameters
        candidate (int): the number of candidates

    Returns:
        full_stmt (tuple): the statement for the ZK proofs in Vote and Obfuscate
    
    """
    g, pk_T, pk_vs, upk, ct_v, ct_lv, ct_lid, ct_i, c0, c1, ct_bar_v, ct_bar_vv = public_params
    r_v, lv, r_lv, r_lid, sk_id, sk_vs = private_params
    R1_range_stmt0, R1_range_stmt1, R1_enc_stmt = [], [], [] 

    #tricks to make the zksk library happy
    one = Secret(value=1)
    neg_c0 = (-1)*c0

    #----------
    #RELATION 1
    #----------

    #PROOF OF VOTE ENCRYPTION  (correctness)
    #(i) proves that each encrypted vote is either 0 or 1
    for i in range(candidates):
        #encryption of 0
        R1_range_stmt0.append(DLRep(ct_v[i][0], r_v*g) & DLRep(ct_v[i][1], r_v*pk_T))
        #encryption of 1
        R1_range_stmt1.append(DLRep(ct_v[i][0], r_v*g) & DLRep(ct_v[i][1] - g, r_v*pk_T))

    #(ii) proves that the sum of all encrypted votes is either 0 or 1 
    elements_c0, elements_c1 = list(map(lambda x: x[0], ct_v)), list(map(lambda x: x[1], ct_v))
    product_c0, product_c1 = reduce(lambda x, y: x + y, elements_c0), reduce(lambda x, y: x + y, elements_c1)
    exp1, exp2= candidates*g, candidates*pk_T
    #encryption of 0
    R1_enc_sum_stmt0 = DLRep(product_c0, exp1*r_v) & DLRep(product_c1, exp2*r_v)
    #encryption of 1
    R1_enc_sum_stmt1 = DLRep(product_c0, exp1*r_v) & DLRep(product_c1 - g, exp2*r_v)

    #flattening of the or-proofs as required by the zksk library and making it also more efficient 
    #instead of proving (R1_range_stmt0_c_0 | R1_range_stmt_1_c_0) & ... & (R1_range_stmt0_c_i | R1_range_stmt_1_c_i) & (R1_enc_sum_stm0 | R1_enc_sum_stm0) 
    #we prove (R1_range_stmt0_c_0 & ... & R1_range_stmt0_c_i & R1_enc_sum_stm0) |  ... | (R1_range_stmt_c_1 & ... & R1_range_stmt0_c_i & R1_enc_sum_stmt1) ) 
    for i in range(candidates):
        if i==0:
            #statement for a vote for the first candidate (1 0 ...  0)  
            R1_enc_stmt.append(R1_enc_sum_stmt1 & R1_range_stmt1[i] & reduce(lambda x, y: x & y, R1_range_stmt0[i+1:]))
        elif i==candidates-1:
            #statement for a vote for the last candidate (0 0 ... 1) 
            R1_enc_stmt.append(R1_enc_sum_stmt1 & R1_range_stmt1[i] & reduce(lambda x, y: x & y, R1_range_stmt0[:i])) 
            #statement for a vote for any other candidate (0 ... 1 ... 0) 
        else: R1_enc_stmt.append(R1_enc_sum_stmt1 & R1_range_stmt1[i] & reduce(lambda x, y: x & y, R1_range_stmt0[:i]) & reduce(lambda x, y: x & y, R1_range_stmt0[i+1:])) 
    #statement for a vote for abstention (0 0 ... 0) 
    R1_enc_stmt.append(R1_enc_sum_stmt0 & reduce(lambda x, y: x & y, R1_range_stmt0[:])) 

    R1_enc_stmt = reduce(lambda x, y: x | y, R1_enc_stmt) 

    #PROOF OF ENCRYPTION   ct_lv = Enc(pk_vs, lv, r_lv) 
    R1_enc_stmt2 = DLRep(ct_lv[0], r_lv*g) & DLRep(ct_lv[1], lv*g + r_lv*pk_vs)

    #PROOF OF RE-ENCRYPTION ct_lid = ReEnc(pk_vs, g*ct_i, r_lid)
    R1_reenc_stmt = DLRep(ct_lid[0], one*ct_i[0] + r_lid*g) & DLRep(ct_lid[1], one*(ct_i[1]+g) + r_lid*pk_vs)

    #PROOF OF KNOWLEDGE upk_id=g*sk_id
    R1_know_stmt = DLRep(upk, sk_id * g)

    #RELATION 1 STATEMENT
    R1_stmt1 = R1_enc_stmt  & R1_enc_stmt2 & R1_reenc_stmt & R1_know_stmt 

    #----------
    #RELATION 2 
    #----------

    #FIRST PROOF OF RE-ENCRYPTION ct_v = ReEnc(pk_T, ct_v-1, r_v)
    R2_reenc_stmt1 = [0]*candidates
    for i in range(candidates):
        R2_reenc_stmt1[i] = DLRep(ct_v[i][0], one*ct_bar_v[i][0] + r_v*g) & DLRep(ct_v[i][1], one*ct_bar_v[i][1] + r_v*pk_T)
    R2_result_stmt1 = reduce(lambda x, y: x & y, R2_reenc_stmt1)

    #SECOND PROOF OF RE-ENCRYPTION ct_lv = ReEnc(pk_vs, ct_i, r_lv)
    R2_reenc_stmt2 = DLRep(ct_lv[0], one*ct_i[0] + r_lv*g) & DLRep(ct_lv[1], one*ct_i[1] + r_lv*pk_vs)

    #THIRD PROOF OF RE-ENCRYPTION ct_lid = ReEnc(pk_vs, ct_i, r_lid)
    R2_reenc_stmt3 = DLRep(ct_lid[0], one*ct_i[0] + r_lid*g) & DLRep(ct_lid[1], one*ct_i[1] + r_lid*pk_vs)

    #PROOF OF DECRYPTION   1 = Dec(sk_id, (ct_lv-1)-(ct_lid-1))
    R2_dec_stmt = DLRep(0*g, one*c1 + sk_vs*neg_c0)

    #RELATION 2 STATEMENT
    R2_stmt = R2_dec_stmt & R2_result_stmt1  &  R2_reenc_stmt2 & R2_reenc_stmt3

    
    #----------
    #RELATION 3 
    #----------

    #FIRST PROOF OF RE-ENCRYPTION ct_v = ReEnc(pk_T, ct_v-2, r_v)
    R3_reenc_stmt1 = [0]*candidates
    for i in range(candidates):
        R3_reenc_stmt1[i] = DLRep(ct_v[i][0], one*ct_bar_vv[i][0] + r_v*g) & DLRep(ct_v[i][1], one*ct_bar_vv[i][1] + r_v*pk_T)
    R3_result_stmt1 = reduce(lambda x, y: x & y, R3_reenc_stmt1)

    #SECOND PROOF OF RE-ENCRYPTION ct_lv = ReEnc(pk_vs, ct_i, r_lv)
    R3_reenc_stmt2 = DLRep(ct_lv[0], one*ct_i[0] + r_lv*g) & DLRep(ct_lv[1], one*ct_i[1] + r_lv*pk_vs)

    #THIRD PROOF OF RE-ENCRYPTION ct_lid = ReEnc(pk_vs, ct_i, r_lid)
    R3_reenc_stmt3 = DLRep(ct_lid[0], one*ct_i[0] + r_lid*g) & DLRep(ct_lid[1], one*ct_i[1] + r_lid*pk_vs)

    #PROOF OF DL INEQUALITY    1 <> Dec(sk_vs, (ct_lv-1)-(ct_lid-1)) 
    R3_dec_stmt = DLNotEqual([pk_vs,g],[c1,c0],sk_vs)
  
    #RELATION 3 STATEMENT
    R3_stmt =  R3_dec_stmt & R3_result_stmt1 & R3_reenc_stmt2 & R3_reenc_stmt3

    return R1_stmt1 | R2_stmt | R3_stmt


def bin_to_int(lst, size):
   """Set the last bit of the binary list lv to 1 as well as any other bit according to the given indexes.
     Converts the binary list to an integer

    Args:
        lst (list): list of indexes
        size (int): size of the binary list

    Returns:
        int: the integer representation of the binary list

   """
   b=[0]*size
   #the new bit is set to 1
   b[-1]=1
   for i in lst:
      b[i]=1  
   return int(''.join(str(bit) for bit in b),2)


def vote(g, order, sk_id, pk_T, pk_vs, v, lv_list, cbr, candidates):
    """Casts a vote and constructs all sub-proofs and witnesses for R1  

    Args:
        g (EcPt): generator of the EC group
        order (Bn): order of the EC group
        sk_id (Bn): secret key of the Voter
        pk_T (EcPt): public key of the Tallier
        pk_vs(EcPt): public key of the Voting Server
        v (int): vote value
        lv_list(): list of indexes
        cbr (): the voter's CBR
        candidates (int): the number of candidates

    Returns:
        ballot: the encrypted vote, the encrypted voter list, the encrypted list id, the NIZK proof

    
    """
    sk = Secret(value=sk_id)
    R1_r_v = Secret(value=order.random())
    R1_r_lv = Secret(value=order.random())
    R1_r_lid = Secret(value=order.random())
    R1_v = [0]*candidates
    for i in  range(candidates):
        R1_v[i] = Secret(value=0)
    if v>0:
        #generate R1_v based on the vote otherwise abstention
        R1_v[v-1] = Secret(value=1)
    #generate lv based on the indexes in lv_list
    R1_lv = Secret(value=bin_to_int(lv_list, len(cbr)+1))

    #last ballot from voter's CBR
    ct_bar_v, ct_bar_lv, ct_bar_lid, ct_bar_proof = cbr[-1]

    #last previous ballot vote
    ct_bar_vv=cbr[-2][0]

    #generating the new ballot
    ct_i = (2*ct_bar_lid[0],2*ct_bar_lid[1]) 
    ct_v = [enc(g, pk_T, R1_v[i].value, R1_r_v.value) for i in range(candidates)]
    ct_lv = enc(g, pk_vs, R1_lv.value, R1_r_lv.value) 
    ct_lid = re_enc(g, pk_vs, (ct_i[0], g+ct_i[1]), R1_r_lid.value)
    c0 = ct_bar_lv[0]-ct_bar_lid[0]
    c1 = ct_bar_lv[1]-ct_bar_lid[1]

    if v>0:
        print(f"[{len(cbr)}] Voted for candidate {v} with voter list {lv_list}") 
    else: print(f"[{len(cbr)}] Voted for no candidate (abstention) with voter list {lv_list}")

    full_stmt=stmt((g, pk_T, pk_vs, sk_id*g, ct_v, ct_lv, ct_lid, ct_i, c0, c1, ct_bar_v, ct_bar_vv), (R1_r_v, R1_lv, R1_r_lv, R1_r_lid, sk, Secret()), candidates)
    simulation_indexes=[]

    #if the vote is for abstention then we need to simulate the proof for all candidates
    simulation_indexes=[i for i in range(candidates)] if v==0 else [i for i in range(candidates+1) if i!=v-1]

    #setting the relations to be simulated
    for i in simulation_indexes:
        full_stmt.subproofs[0].subproofs[0].subproofs[i].set_simulated()
    full_stmt.subproofs[1].set_simulated()
    full_stmt.subproofs[2].set_simulated()
    
    #constructing the witness for each candidate vote encryption 
    R1_v_str=[('R1_v'+str([i]), R1_v[i].value) for i in range(candidates)]
    sec_dict=dict(R1_v_str)

    #prove the statement
    nizk = full_stmt.prove(sec_dict.update({R1_r_v: R1_r_v.value, R1_lv: R1_lv.value, R1_r_lv: R1_r_lv.value, R1_r_lid: R1_r_lid.value, sk: sk.value}))

    return (ct_v, ct_lv, ct_lid, nizk)
           
def obfuscate(g, order, cbr, sk_vs, upk, pk_T, pk_vs, candidates):
   """Cast a ballot obfuscation and constructs all sub-proofs and witnesses for R2 or R3
    
    Args:
        g (EcPt): generator of the EC group
        order (Bn): order of the EC group
        cbr (): the voter's CBR
        sk_vs (Bn): secret key of the Voting Server
        upk (EcPt): public key of the Voter
        pk_T (EcPt): public key of tallier
        pk_vs (EcPt): public key of the Voting Server
        candidates (int): number of candidates

    Returns:
        ballot: the encrypted vote, the encrypted voter list, the encrypted list id, the NIZK proof
   """
   r_v = Secret(value=order.random())
   r_lv = Secret(value=order.random())
   r_lid = Secret(value=order.random())
   sk = Secret(value=sk_vs)
   
   #last ballot from voter's CBR 
   ct_bar=cbr[-1]

   if len(cbr)<2:
       #if there is no last previous ballot then we use the last ballot as the previous ballot
       ct_bar2=ct_bar
   else: ct_bar2=cbr[-2]

   ct_bar_lv, ct_bar_lid = ct_bar[1], ct_bar[2]

   ct_i=(2*ct_bar_lid[0],2*ct_bar_lid[1])  
   ct_lv=re_enc(g, pk_vs, ct_i, r_lv.value) 
   ct_lid=re_enc(g, pk_vs, ct_i, r_lid.value) 

   c0 = ct_bar_lv[0]-ct_bar_lid[0]
   c1 = ct_bar_lv[1]-ct_bar_lid[1]
   ct = (c0, c1)
   g_m_dec = dec(ct, sk.value)

   if g_m_dec==0*g:
    #if 1 = Dec(sk_vs, (ct_lv-1)-(ct_lid-1)) then we re-randomize the last ballot 
    ct_bar_v=ct_bar[0]
    sim_relation=2
    print(f"[{len(cbr)}] VS obfuscated last ballot")
   else : 
    ct_bar_v=ct_bar2[0]
    sim_relation=1
    print(f"\033[31m[{len(cbr)}] VS obfuscated previous last ballot\033[0m")
    
   ct_v = [re_enc(g, pk_T, ct_bar_v[i], r_v.value) for i in range(candidates)]

   full_stmt=stmt((g, pk_T, pk_vs, upk, ct_v, ct_lv, ct_lid, ct_i, c0, c1, ct_bar[0], ct_bar2[0]),(r_v, Secret(), r_lv, r_lid, Secret(), sk), candidates )
   full_stmt.subproofs[0].set_simulated()
   
   #depending on whether 1 = Dec(sk_vs, (ct_lv-1)-(ct_lid-1)) or not we simulate R2 or R3, other than R1
   full_stmt.subproofs[sim_relation].set_simulated()
   nizk = full_stmt.prove({r_v: r_v.value, r_lv: r_lv.value, r_lid: r_lid.value, sk: sk.value})

   return (ct_v, ct_lv, ct_lid, nizk)
   

def stmt_tally(g, order, votes, c0, c1, sk_T):
    """Constructs the statement for the ZK proofs in Tally

    Args:
        g (EcPt): generator of the EC group
        order (Bn): order of the EC group
        votes (int): number of votes for a candidate
        c0 (EcPt): sum of all encrypted votes for a candidate
        c1 (EcPt): sum of all encrypted votes for a candidate
        sk_T (Bn): secret key of the Tallier

    Returns:
        full_stmt (tuple): the statement for the ZK proofs in Tally

    """
    one=Secret(value=1)
    neg_c0 = (-1)*c0
    return DLRep(votes*g, one*c1 + sk_T*neg_c0)

def tally(g, order, sk_T, ballots, candidates, voters):
    """Tally the votes and constructs all sub-proofs and witnesses for Tally
    
    Args:
        g (EcPt): generator of the EC group
        order (Bn): order of the EC group
        sk_T (Bn): secret key of the Tallier
        ballots (): the last ballots from all voter CBRs
        candidate (int): number of candidates
        voters (int): number of registered voters

    Returns:
        votes (list): the number of votes for each candidate
        nizk (list): the NIZK proofs for each candidate

    """
    sk=Secret(value=sk_T)
    stmt, nizk=[], []
    votes_for_candidate=[0]*candidates
    
    for i in range(candidates):
        c0, c1 =(0*g), (0*g)

        #summing up all encrypted votes for a candidate
        for j in range(voters):
            c0+=ballots[j][i][0]
            c1+=ballots[j][i][1]
        sum_votes=dec((c0,c1), sk_T)

        #finding the number of votes for a candidate
        for j in range(voters):
            if sum_votes==j*g:
                votes_for_candidate[i]=j
                break

        print("Votes for Candidate",i+1,":", votes_for_candidate[i])

        #constructing the statement for the ZK proof
        stmt.append(stmt_tally(g, order, j,c0, c1, sk))

        #proving the statement
        nizk.append(stmt[-1].prove({sk: sk.value}))

    print("Abstention votes:", voters-sum(votes_for_candidate)) 
    return votes_for_candidate, nizk


