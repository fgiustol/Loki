from loki import * 

"""
 Each line of vCBR is the CBR of a voter
     0 indicates abstention vote 
    -1 indicates an obfuscation
    (x,[y1, ..., y2]]) indicates a vote for candidate x and a list of indexes y1,...y2  

"""

"""========================="""
"""EXAMPLE FROM PAPER FIG. 1"""
"""========================="""
vCBR = [
    (2, -1, -1, (1, []), -1, -1, -1, -1, (2, []), -1, -1), #cand1
    (0, -1, -1, -1, -1, -1, -1, (2, []), -1, -1, (0, [7]), -1, -1), #abst 
    (0, -1, -1, -1, (1, []), -1, (2, [4]),  -1, -1, -1, -1, -1, -1, (1, [4]), -1, -1), #cand2
    (0, -1, -1, -1, -1, -1, -1, -1, -1, -1) #abst
]


#number of candidates (should be 2 or more)
candidates = 2 

#number of voters (should be 2 or more)
voters = len(vCBR)

CBR = [[] for i in range(voters)]

print("--------------------")
print("Candidates:", candidates, "Voters:", voters)
print("--------------------")

#SETUP
g, order, pk_vs, sk_vs, sk_T, pk_T = setup()



#REGISTRATION

#Generating a keypair for each voter
usk = [order.random() for i in range(voters)]
upk = [usk[i]*g for i in range(voters)]


#Init for avg time computation
e_time_obf = []
e_time_vote = []



#VOTING

for voter in range(voters):
    print(f"\nVoter {voter}")

    for i, element  in enumerate(vCBR[voter]):
     #obfuscation   
     if element == -1:
         s_time_obf = time.process_time_ns()
         CBR[voter].append(obfuscate(g, order, CBR[voter],sk_vs, upk[voter], pk_T, pk_vs, candidates))
         e_time_obf.append(time.process_time_ns() - s_time_obf)
     #vote    
     elif isinstance(element,tuple): 
         s_time_vote = time.process_time_ns()
         CBR[voter].append(vote(g, order, usk[voter], pk_T, pk_vs, vCBR[voter][i][0], vCBR[voter][i][1], CBR[voter], candidates))
         e_time_vote.append(time.process_time_ns() - s_time_vote)
     #CBR initialization     
     else:
         r0 = order.random()
         x = [0]*candidates
         #initialization with a candidate instead of 0 (simulates coercion at registration, not available in Loki but possible in theory) 
         if element>0: 
             x[element-1] = 1
         ct0 = [enc(g, pk_T, x[j], r0) for j in range(candidates)]
         ctl0 = enc(g, pk_vs, 0, r0)
         bar_ct = (ct0, ctl0, ctl0, r0)
         CBR[voter].append(bar_ct)                
         print(f"[{i}] Initialization ballot ({element})") 




#BALLOT VERIFICATION

#keep track of failed verifications
failed = []

for i in range(voters):
    for idx, cbr in enumerate(CBR[i][1:], start=1):  
        if i == 0 and idx == 1:
            s_time_verify = time.process_time_ns()

        ct_bar = CBR[i][idx - 1]
        ct_bar_v, ct_bar_lv, ct_bar_lid, ct_bar_proof = ct_bar
        ct_i = (2 * ct_bar_lid[0], 2 * ct_bar_lid[1])
        c0, c1 = ct_bar_lv[0] - ct_bar_lid[0], ct_bar_lv[1] - ct_bar_lid[1]
        
        # last previous ballot from voter's CBR if it exists, otherwise the last ballot is also the last previous ballot
        ct_bar2 = CBR[i][idx - 1] if idx == 1 else CBR[i][idx - 2]
        ct_bar_vv = ct_bar2[0]
    
        stmt_c = stmt((g, pk_T, pk_vs, upk[i], cbr[0], cbr[1], cbr[2], ct_i, c0, c1, ct_bar_v, ct_bar_vv), 
                      (Secret(), Secret(), Secret(), Secret(), Secret(), Secret()), candidates)

        if i == 0 and idx == 1:
            e_time_verify = time.process_time_ns() - s_time_verify

        if not stmt_c.verify(cbr[3]):
            failed.append((i, cbr))

if failed:
    for i, cbr in failed:
        print(f"\nVerification failed for voter {i}'s CBR at index {CBR[i].index(cbr)}") 
else:
    print("\nVerification successful for all ballots in every voter's CBR")


#TALLYING

print("\nTallying...")
s_time_tally = time.process_time_ns()
last_ballots = [sublist[-1][0] for sublist in CBR]
votes, nizk=tally(g,order,sk_T, last_ballots,candidates,voters)
e_time_tally = time.process_time_ns() - s_time_tally

#Tally verification
s_time_tally_verification = time.process_time_ns()
stmt=[]
for i in range(candidates):
        c0, c1 =(0*g), (0*g)
        for j in range(voters):
            c0+=last_ballots[j][i][0]
            c1+=last_ballots[j][i][1]
        stmt.append(stmt_tally(g, order, votes[i],c0, c1, Secret()))

for i in range(candidates):
    print(f"Verification for tallying of votes for candidate {i+1}: {stmt[i].verify(nizk[i])}")
e_time_tally_verification = time.process_time_ns() - s_time_tally_verification


#TIMINGS

print(f"\nTimings")
print("=======")
print("Ballot obfuscation time (avg):", round(sum(e_time_obf)/len(e_time_obf)/1000000,3), "ms")
print("Ballot vote time (avg):", round(sum(e_time_vote)/len(e_time_vote)/1000000,3), "ms")
print("Ballot verification time:", e_time_verify/1000000, "ms")
print("Tallying time:", e_time_tally/1000000, "ms")
print("Tallying verification time:", e_time_tally_verification/1000000, "ms")
print("=======")


