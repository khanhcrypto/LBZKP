# This is the script for computing the non-interactive proof size
# of proving knowledge of a MLWE sample described in Section 6.2.
# Concretely, we want to prove knowledge of a vector s such that
# norm of ||(s,As-u)|| is at most B.

# Computing the root Hermite factor based on the BKZ block size

def GSAhermite(bs):
  return (bs/(2*pi*exp(1))*(pi*bs)^(1/bs))^(1/(2*bs-2))

def BDGLcost(bs):
  return bs*log(sqrt(3/2),2)

def FindMSISdelta(m, n, q, b):
    kappa = 0
    b2 = 0
    logq = log(q,2)
    best = 9999
    root_hermite_factor = 10
    if b+b2 >= (q-1)/2:
        return root_hermite_factor
    for i in range(m+1,n + 5,5):
        for bs in range(50, max(i,1000) + 5, 5):
            cost = BDGLcost(bs)
            if cost >= best:
                break
            h = 2*log(GSAhermite(bs),2)
            d = min(i, floor(-0.5 + sqrt(0.25+2*m*logq/h)))                     # h * d*(d+1)/2 = m*logq
            l = d*h + (m*logq - (d^2+d)/2*h)/d
            sig = exp(l)/sqrt(d)
            p  = 1 - erfc(b/(sqrt(2)*sig))
            p2  = 1 - erfc((b+b2)/(sqrt(2)*sig))
            s = ceil((15*sig/q+0.5)/10)
            for j in range(1,10*s + s,s):
                p += s*(erfc((i*q-b)/(sqrt(2)*sig)) - erfc((i*q+b)/(sqrt(2)*sig)))
                p2 += s*(erfc((i*q-b-b2)/(sqrt(2)*sig)) - erfc((i*q+b+b2)/(sqrt(2)*sig)))
            p2 -= p
            s = 0
            for i in range (0,kappa+1):
                s += binomial(d,i)*p^(d-i)*p2^i
            cost -= min(0,log(s,2) + bs/2*log(4/3),2)
            if cost < best:
                best = cost 
                bbs = bs
                bd = d
                sisdim = i
                root_hermite_factor = GSAhermite(bbs)
            print("SIS hardness in inf norm:");
            print("  SIS lattice dimension used: ", sisdim);
            print("  Number of non-zero Gram-Schmidt vectors: ", bd);
            print("  Root Hermite factor: ", round(GSAhermite(bbs),6));
            print("  BKZ block size:", bbs);
            print("  Cost: ", best);
    return root_hermite_factor
        

# Function for estimating the MSIS hardness given parameters:
# a (n x m) matrix in \Rq along with the solution bound B. It returns the
# root Hermite factor \delta. We use the methodology presented by
# [GamNgu08, Mic08] and hence m is irrelevant.

#def findMSISdelta(B, n, d, logq):
#	logC = log(B, 2)		
#	logdelta = logC^2 / (4*n*d*logq)
#	return 2^logdelta

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
eta = 158                               # the heuristic bound on \sqrt[2k](|| \sigma_{-1}(c^k)*c^k ||_1) for k = 32

# Defining the log of the proof system modulus -- finding true values will come later 
nbofdiv = 1                             # number of prime divisors of q, usually 1 or 2
logq1 = 32                              # log of the smallest prime divisor of q
logq = 32                               # log of the proof system modulus q
lmbda = 2 * ceil( secpam/(2*logq) )     # number of repetitions for boosting soundness, we assume lambda is even

# Length and size of the committed messages
m1 = 16                                 # length of s1
ell = 0                                 # length of m 
alpha = sqrt(1024)                      # norm of s1

# Parameters for proving norm bounds
v_e = 1                                 # number of exact norm proofs 
BoundsToProve =[ sqrt(2048) ]           # exact bounds beta_i to prove
k_bin = 0                               # length of a vector to prove binary coefficients                           
B_exact = sqrt(2048 + 128)              # bound alpha^(e) on the vector e^(e) = (s,As - u, bin. decomp. of B^2 - ||(s,As-u)||^2)
N = 16 + 1                              # length of the vector e^(e)
approximate_norm_proof = 0              # boolean to indicate if we perform approximate norm proofs
B_approx = 1                            # bound alpha^(d) on the vector e^(d), we set it to be 1 if the boolean is zero

# Parameters for rejection sampling
gamma1 = 11                             # rejection sampling for s1
gamma2 = 1.85                           # rejection sampling for s2
gammae = 5                              # rejection sampling for Rs^(e)
gammad = 1                              # rejection sampling for R's^(d) -- ignore if approximate_norm_proof = 0 

# Setting the standard deviations, apart from stdev2 
stdev1 = gamma1 * eta * sqrt(alpha^2 + v_e *d)
stdev2 = 0
stdeve = gammae * sqrt(337) * B_exact
stdevd = gammad * sqrt(337) * B_approx 

# Finding MLWE dimension
nu = 1                                 # randomness vector s2 with coefficients between -nu and nu
kmlwe = 1                              # dimension of the Module-LWE problem
mlwe_hardness = 2
while mlwe_hardness > 1.0045:
    kmlwe += 1                         # increasing the kmlwe dimension until MLWE provides ~ 128-bit security
    mlwe_hardness = findMLWEdelta(nu,kmlwe,d, logq)

# Finding an appropriate n and gamma
gamma = (2^logq / (2 * kappa * d ) - 2) / 4 - 2^10                                                            # we pick gamma such that 4*kappa*d*(4*gamma + 2) < q/2 
n = 0                                                                                                    # dimension of the Module-SIS problem
secure = false
while secure == false:
    n += 1
    m2 = kmlwe + n + ell + lmbda/2 + 256/d + 1 + approximate_norm_proof * 256/d + 1                      # we use the packing optimisation from Section 5.3            
    stdev2 = gamma2 * eta * nu * sqrt(m2 * d)
    Bound1 = 4 * eta * 2 * stdev1 * sqrt(2 * (m1 + v_e) * d)
    Bound2 = 4 * eta * 2 * stdev2 * sqrt(2 * m2 * d)
    Bound_infty = 4 * kappa * d * (4 * gamma + 2)
    Bound = max(Bound1,Bound2,Bound_infty)
    if FindMSISdelta(n*d,(m1+m2)*d,2^logq,Bound) < 1.0045 and Bound < 2^logq:                            # increasing n until we reach ~ 128-bit security
        secure = true                                                                                   

# Finding exact value for q, q1 and gamma and Dilithium compression variables:
find_true_gamma = 0
q1 = 2^(logq1)
while find_true_gamma == 0:
    q1 =  4*l * int(2^(log(q1,2)) / (4*l)) + 2*l + 1                                                     # we need q1 to be congruent to 2l+1 modulo 4l
    while is_prime(q1) == False :
        q1 -= 4*l
    if nbofdiv == 1:
        q = q1
    else:
        q2 = 4*l * int(2^(logq)/(4*l*q1)) + 2*l  + 1                                                     # we need q2 to be congruent to 2l+1 modulo 4l
        while is_prime(q2) == False :
            q2 -= 4*l
        q = q1 * q2 
    Div_q = divisors( (q-1)/2)                                                                           # we want to find a divisor of (q-1)/2 close to gamma
    for i in Div_q:
        if gamma/2 < i and i <= gamma:
            find_true_gamma = i
gamma = find_true_gamma 
D = int( log(2*gamma/(kappa*d), 2) )
tau = kappa * nu * d

# Checking knowledge soundness conditions
t = sqrt( 1 - log(2^(-secpam)) / 128 )                 
Barp = 2 * sqrt(256/26) * t * stdeve 

if q <  41 * N * d * Barp:
    print("ERROR: can't use Lemma 2.2.8")

if q <= Barp^2 + Barp*sqrt(k_bin*d):
    print("ERROR: can't prove E_bin*s + v_bin has binary coefficients")

if q <= Barp^2 + Barp*sqrt(d):
    print("ERROR: can't prove all x_i have binary coefficients")

for bound in BoundsToProve:
    if q <= 3 * bound^2 + Barp^2:
        print("ERROR: can't prove || E_i*s - v_i || <= beta_i")



print("---------- computed parameters ----------")
print("q1: ", q)
print("q: ", q)
print("gamma: ", gamma)
print("D: ", D)
print("tau: ", tau)
print("n: ", n)
print("kmlwe: ", kmlwe)

print("---------- security analysis ----------")

# Repetition rate
rep_rate = 2*exp(14/gamma1 + 1/(2*gamma1^2)) * exp(1/(2*gamma2^2)) * exp(1/(2*gammae^2)) * ((1-approximate_norm_proof) + approximate_norm_proof*exp(1/(2*gammad^2)))
rep_rate = rep_rate * exp( n * (2*tau + 1) * d / (2*gamma) )
print("Repetition rate: ", round(rep_rate ,2 ))

# Knowledge soundness error from Theorem 5.3
soundness_error = 2 * 1/(2*kappa+1)^(d/2) +  q1^(-d/l) + q1^(-lmbda) + 2^(-128) + approximate_norm_proof*2^(-256)
print("Log of the knowledge soundness error: ", ceil(log(soundness_error, 2)) )

# MSIS hardness
Bound1 = 4 * eta * 2 * stdev1 * sqrt(2 * (m1 + v_e) * d)
Bound2 = 4 * eta * 2 * stdev2 * sqrt(2 * m2 * d)
Bound_infty = 4 * kappa * d * (4 * gamma + 2)
Bound = max(Bound1,Bound2,Bound_infty)
print("Root Hermite factor for MSIS: ", round(FindMSISdelta(n*d,(m1+m2)*d,q,Bound),6)) 
print("Root Hermite factor for MLWE: ", round(mlwe_hardness,6)) 
# Proof size
print("---------- proof size ----------")
GaussEntr = 4.13
full_sized = n * d * (logq - D) + (ell + 256/d + 1 + approximate_norm_proof * 256/d + lmbda + 1) * d * logq    
short_size1 = (m1 + v_e) * d * ceil(log(GaussEntr * stdev1,2)) + (m2 - n) * d * ceil(log(GaussEntr * stdev2,2)) 
short_size2 = 256 * ceil(log(GaussEntr * stdeve,2)) + approximate_norm_proof * 256 * ceil(log(GaussEntr * stdevd,2))

print("Total proof size in KB: ", round((full_sized + short_size1 + short_size2)/(2^13) , 2))