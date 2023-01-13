# This is the script for computing the non-interactive proof size
# of proving knowledge of a MLWE sample described in Section 6.2.
# Concretely, we want to prove knowledge of a vector s such that
# norm of ||(s,As-u)|| is at most B.


# Function for estimating the MSIS hardness given parameters:
# a (n x m) matrix in \Rq along with the solution bound B. It returns the
# root Hermite factor \delta. We use the methodology presented by
# [GamNgu08, Mic08] and hence m is irrelevant.

def findMSISdelta(B, n, d, logq):
	logC = log(B, 2)		
	logdelta = logC^2 / (4*n*d*logq)
	return 2^logdelta

# Function for estimating the MLWE hardness for a (m x n) matrix in \Rq and 
# secret coefficients sampled uniformly at random between -nu and nu.
# We use the LWE-Estimator by [AlbPlaSco15] as a black-box.

def findMLWEdelta(nu, n, d, logq):
    load("https://bitbucket.org/malb/lwe-estimator/raw/HEAD/estimator.py")
    n = n * d
    q = 2^logq
    stddev = sqrt(((2*nu+1)^2 - 1)/12)
    alpha = alphaf(sigmaf(stddev),q)
    set_verbose(1)
    L = estimate_lwe(n, alpha, q, reduction_cost_model=BKZ.enum)
    delta_enum1 = L['usvp']['delta_0'] 
    delta_enum2 = L['dec']['delta_0']  
    delta_enum3 = L['dual']['delta_0']  
    L = estimate_lwe(n, alpha, q, reduction_cost_model=BKZ.sieve)
    delta_sieve1 = L['usvp']['delta_0'] 
    delta_sieve2 = L['dec']['delta_0']  
    delta_sieve3 = L['dual']['delta_0']
    return max(delta_enum1,delta_enum2,delta_enum3,delta_sieve1,delta_sieve2,delta_sieve3)




# Security parameter, ring dimension of \R and challenge space
secpam = 128                            # security parameter
d = 128                                 # dimension of R = Z[X]/(X^d + 1)
l = 2                                   # number of irreducible factors of X^d + 1 modulo each q_i, we assume each q_i = 2l+1 (mod 4l)
kappa = 2                               # maximum coefficient of a challenge. We want |\chal| = (2*kappa+1)^(d/2) >= 2^secpam
eta = 59                                # the heuristic bound on \sqrt[2k](|| \sigma_{-1}(c^k)*c^k ||_1) for k = 32

# Defining the log of the proof system modulus -- finding true values will come later 
nbofdiv = 1                             # number of prime divisors of q, usually 1 or 2
logq1 = 32                              # log of the smallest prime divisor of q
logq = 32                               # log of the proof system modulus q
lmbda = 2 * ceil( secpam/(2*logq1) )    # number of repetitions for boosting soundness, we assume lambda is even

# Length and size of the committed messages
m1 = 8                                  # length of s1
m2 = 0                                  # length of s2, to be determined
ell = 0                                 # length of m 
alpha = sqrt(1024)                      # norm of s1

# Parameters for proving norm bounds
ve = 1                                  # number of exact norm proofs 
BoundsToProve = [sqrt(2048)]            # exact bounds beta_i to prove for i=1,2,...,ve
k_bin = 0                               # length of a vector to prove binary coefficients                           
alphae = sqrt(2048 + ve*d)              # bound alpha^(e) on the vector e^(e) = (s,As - u, bin. decomp. of B^2 - ||(s,As-u)||^2)
ce = 16 + ve                            # length of the vector e^(e)
approximate_norm_proof = 0              # boolean to indicate if we perform approximate norm proofs
alphad = 1                              # bound alpha^(d) on the vector e^(d), we set it to be 1 if the boolean is zero

# Parameters for rejection sampling
gamma1 = 19                             # rejection sampling for s1
gamma2 = 2                              # rejection sampling for s2
gammae = 2                              # rejection sampling for Rs^(e)
gammad = 1                              # rejection sampling for R's^(d) -- ignore if approximate_norm_proof = 0 

# Setting the standard deviations, apart from stdev2
stdev1 = gamma1 * eta * sqrt(alpha^2 + ve *d)
stdev2 = 0
stdeve = gammae * sqrt(337) * alphae
stdevd = gammad * sqrt(337) * alphad 

# Finding MLWE dimension
print("Computing the Module-LWE dimension...")
nu = 1                                  # randomness vector s2 with coefficients between -nu and nu
mlwe =  9                               # dimension of the Module-LWE problem
mlwe_hardness = 2
while mlwe_hardness > 1.0045:           # increasing the mlwe dimension until MLWE provides ~ 128-bit security
    mlwe += 1                          
    mlwe_hardness = findMLWEdelta(nu,mlwe,d, logq)
    
    
    

# Finding an appropriate Module-SIS dimension n
print("Computing the Module-SIS dimension...")
n = 0                                                                                     # dimension of the Module-SIS problem
D = 0                                                                                     # dropping low-order bits of t_A
gamma = 0                                                                                 # dropping low-order bits of w
value_n_found = false                                                                     # Boolean for finding n
while value_n_found == false:                                                             # searching for n
    n += 1                                                                                
    m2 = mlwe + n + ell + lmbda/2 + 256/d + 1 + approximate_norm_proof * 256/d + 1        # we use the packing optimisation from Section 5.3            
    stdev2 = gamma2 * eta * nu * sqrt(m2 * d)                                             # set stdev2 with the current candidate for n
    Bound1 =  2 * stdev1 * sqrt(2 * (m1 + ve) * d)                                        # bound on bar{z}_1
    Bound2 =  2 * stdev2 * sqrt(2 * m2 * d) + 2^D * eta * sqrt(n*d) + gamma * sqrt(n*d)   # bound on bar{z}_2 = (bar{z}_{2,1},bar{z}_{2,2})
    Bound = 4 * eta * sqrt(Bound1^2 + Bound2^2)                                           # bound on the extracted MSIS solution
    if findMSISdelta(Bound,n,d,logq) < 1.0045 and Bound < 2^logq:                         # until we reach ~ 128-bit security
        value_n_found = true                                                              # it is secure 




# Given n, find the largest possible gamma which makes the MSIS solution still small
print("Computing the parameter gamma...")
gamma = 2^logq                                                                            # initialisation
value_gamma_found = false                                                                 # Boolean for finding gamma
while value_gamma_found == false:                                                         # searching for right gamma
    gamma /= 2                                                                            # decrease the value of gamma    
    Bound1 =  2 * stdev1 * sqrt(2 * (m1 + ve) * d)                                        # bound on bar{z}_1
    Bound2 =  2 * stdev2 * sqrt(2 * m2 * d) + 2^D * eta * sqrt(n*d) + gamma * sqrt(n*d)   # bound on bar{z}_2
    Bound = 4 * eta * sqrt(Bound1^2 + Bound2^2)                                           # bound on the extracted MSIS solution
    if findMSISdelta(Bound,n,d,logq) < 1.0045 and Bound < 2^logq:                         # until we reach ~ 128-bit security
        value_gamma_found = true                                                          # it is secure


# Finding exact values for q, q1 and gamma:
print("Computing moduli q1, q etc. ...")
true_gamma_found = false                                                                  # Boolean for finding correct gamma
q1 = 2^(logq1) + (2*l + 1)                                                                # we need q1 to be congruent to 2l+1 modulo 4l
while true_gamma_found == false:
    q1 =  q1 - 4*l                                                                        # find the next candidate for q1
    while is_prime(q1) == False :                                                         # we need q1 to be prime 
        q1 -= 4*l
    if nbofdiv == 1:                                                                      # if number of divisors of q is 1, then q = q1
        q = q1
    else:
        q2 = 4*l * int(2^(logq)/(4*l*q1)) + 2*l  + 1                                      # we need q2 to be congruent to 2l+1 modulo 4l
        while is_prime(q2) == False :                                                     # we need q2 to be prime
            q2 -= 4*l
        q = q1 * q2                                                                       # if number of divisors of q is 2, then q = q1*q2 
    Div_q = divisors(q-1)                                                                 # consider divisors of q-1
    for i in Div_q:                 
        if gamma*4/5 < i and i <= gamma and is_even(i):                                   # find a divisor which is close to gamma
            gamma = i                                                                     # we found a good candidate for gamma
            true_gamma_found = true


# Given n and gamma, find the largest possible D which makes the MSIS solution small
print("Computing the parameter D...")
D = logq                                                                                        # initialisation
value_D_found = false                                                                           # Boolean for finding D
while value_D_found == false:                                                                   # searching for right D
    D -= 1                                                                                      # decrease the value of D
    Bound1 =  2 * stdev1 * sqrt(2 * (m1 + ve) * d)                                              # bound on bar{z}_1
    Bound2 =  2 * stdev2 * sqrt(2 * m2 * d) + 2^D * eta * sqrt(n*d) + gamma * sqrt(n*d)         # bound on bar{z}_2
    Bound = 4 * eta * sqrt(Bound1^2 + Bound2^2)                                                 # bound on the extracted MSIS solution
    if findMSISdelta(Bound,n,d,logq) < 1.0045 and Bound < 2^logq and 2^(D-1)*kappa*d < gamma:   # until we reach ~ 128-bit security                                           
        value_D_found = true                                                                    # it is secure



# Checking knowledge soundness conditions from Theorem 5.3
print("Checking knowledge soundness conditions...")
t = 1.64                 
Be = 2 * sqrt(256/26) * t * stdeve 

if q <  41 * ce * d * Be:
    print("ERROR: can't use Lemma 2.9")

if q <= Be^2 + Be*sqrt(k_bin*d):
    print("ERROR: can't prove E_bin*s + v_bin has binary coefficients")

if q <= Be^2 + Be*sqrt(ve*d):
    print("ERROR: can't prove all x_i have binary coefficients")

for bound in BoundsToProve:
    if q <= 3 * bound^2 + Be^2:
        print("ERROR: can't prove || E_i*s - v_i || <= beta_i")



# Output computed parameters 
print("---------- computed parameters ----------")
print("The smallest prime divisor q1 of q: ", q1)
print("Proof system modulus q: ", q)
print("Parameter gamma for dropping low-order bits of w: ", gamma)
print("Parameter D for dropping low-order bits of t_A : ", D)
print("Module-SIS dimension: ", n)
print("Module-LWE dimension: ", mlwe)
print("Length of the randomness vector s2: ", m2)
print("Log2 of the standard deviation stdev1: ",round(log(stdev1,2),2))
print("Log2 of the standard deviation stdev2: ",round(log(stdev2,2),2))
print("Log2 of the standard deviation stdeve: ",round(log(stdeve,2),2))


# Output security analysis
print("---------- security analysis ------------")

# Repetition rate
rep_rate = 2*exp(14/gamma1 + 1/(2*gamma1^2)) * exp(1/(2*gamma2^2)) * exp(1/(2*gammae^2)) * ((1-approximate_norm_proof) + approximate_norm_proof*exp(1/(2*gammad^2)))
print("Repetition rate: ", round(rep_rate ,2 ))

# Knowledge soundness error from Theorem 5.3
soundness_error = 2 * 1/(2*kappa+1)^(d/2) +  q1^(-d/l) + q1^(-lmbda) + 2^(-128) + approximate_norm_proof*2^(-256)
print("Log of the knowledge soundness error: ", ceil(log(soundness_error, 2)) )

# Exact Module-SIS and Module-LWE hardness
Bound1 =  2 * stdev1 * sqrt(2 * (m1 + ve) * d)
Bound2 =  2 * stdev2 * sqrt(2 * m2 * d) + 2^D * eta * sqrt(n*d) + gamma * sqrt(n*d)
Bound = 4 *  eta * sqrt(Bound1^2 + Bound2^2)
print("Root Hermite factor for MSIS: ", round( findMSISdelta(Bound,n,d,logq) ,6)) 
print("Root Hermite factor for MLWE: ", round(mlwe_hardness,6)) 



# Proof size
print("---------- proof size -------------------")
full_size = n * d * (logq - D) + (ell + 256/d + 1 + approximate_norm_proof * 256/d + lmbda + 1) * d * logq   
challenge = ceil(log(2*kappa+1,2)) * d 
short_size1 = (m1 + ve) * d * (ceil(log(stdev1,2) + 2.57)) + (m2 - n) * d * (ceil(log(stdev2,2) + 2.57)) 
short_size2 = 256 * (ceil(log(stdeve,2) + 2.57)) + approximate_norm_proof * 256 * (ceil(log(stdevd,2) + 2.57))
hint = 2.25 * n * d

print("Total proof size in KB: ", round((full_size + challenge + short_size1 + short_size2 + hint)/(2^13) , 2))
print("full-sized polynomials in KB: ", round(full_size/(2^13) , 2))
print("challenge c in KB: ", round(challenge/(2^13) , 2))
print("short-sized polynomials in KB: ", round((short_size1 + short_size2 + hint)/(2^13) , 2))