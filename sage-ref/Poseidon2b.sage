import re
from Crypto.Hash import SHAKE128, TurboSHAKE256
import math

# -------------------------------------------------------------------------------------------
# Code to create round constants
# -------------------------------------------------------------------------------------------
class ShakeUtils:
    def __init__(self, init_shake, p, n):
        """
        Initialize ShakeUtils with an adjustable INIT_SHAKE and field size.
        """
        self.init_shake = init_shake
        self.field_size = p**n
        self.num_bytes = math.ceil(self.field_size.bit_length() / 8)  # Enough bytes to cover the field_size
        self.endianess = 'little'

    def init_shake_reader(self):
        """
        Initialize a SHAKE reader with the adjustable INIT_SHAKE.
        """
        #shake = SHAKE128.new()
        shake = TurboSHAKE256.new(domain=0x1F)
        shake.update(self.init_shake.encode('utf-8'))
        for value in self.get_field_size_in_chunks():
            shake.update(int(value).to_bytes(length=8, byteorder=self.endianess))
        return shake

    def get_field_size_in_chunks(self):
        """
        Retrieve the field size, split up in 8 byte chunks.
        """
        o = self.field_size
        order = []
        while o != 0:
            o_ = o & (2**64-1)
            order.append(o_)
            o >>= 64
        return order

    def get_field_element_from_shake(self, reader):
        """
        Generate integer representation of a field element (int less than field size) from the SHAKE reader.
        """
        while True:
            buf = bytearray(reader.read(self.num_bytes))
            value = int.from_bytes(buf, self.endianess)  # Convert bytes to integer
            if value < self.field_size:  # Ensure the value is within the field
                return value

    def get_random_elements(self, num_values, shake):
        """
        Generate round constants using the SHAKE reader.
        """
        return [self.get_field_element_from_shake(shake) for _ in range(num_values)]

    
# -------------------------------------------------------------------------------------------
# Code to check matrices
# -------------------------------------------------------------------------------------------
#https://extgit.isec.tugraz.at/krypto/linear-layer-tool
def isAllInvertible(M, t):
    """
    Test all square submatrices for invertibility. If fulfilled, matrix is MDS.
    """
    counter = 0
    all_invertible = True
    for i in range(2, t):
        choices_i = Combinations(range(0, t), i)
        for m in range(0, choices_i.cardinality()):
            for n in range(0, choices_i.cardinality()):
                M_sub = M[choices_i[m], choices_i[n]]
                is_inv = M_sub.is_invertible()
                all_invertible = all_invertible and is_inv
                #if is_inv == False:
                    #print("FALSE")
                    #print(M_sub)
                counter += 1
    #print("Submatrices checked:", counter)
    return all_invertible


def getLengthSubspaceTrail(F, M, t):
    """
    Get the length of the subspace trail for matrix M.
    """
    S = [F^t]  # S^(0)
    #print(f"Trivial subspace S^({len(S)-1}):", S[-1], "\n")
    
    M_pow = Matrix.identity(F, t) # M^0
    K = []  # Kernel matrix

    while S[-1].dimension() > 1:
        K.append(M_pow[0]) # add first row
        S.append(matrix(F,K).right_kernel())
        #print(f"Subspace S^({len(S)-1}):", S[-1], "\n")
        M_pow = M * M_pow  # M^i
    
    # If next step stays the same, we have infinite subspace trail
    K.append(M_pow[0]) # add first row
    S_next = matrix(F,K).right_kernel()
    #print(f"Subspace S^({len(S)}):", S_next, "\n")
    
    if S_next.dimension() == 0:
        #print(f"Found subspace trail of length max {len(S)-1}")
        return len(S)-1, S[-1].dimension()
    if S_next.dimension() == 1:
        #print(f"Found infinite subspace trail")
        return math.inf, S[-1].dimension()


def check_MP(F, M, t, need_mds=False, need_inv=True, debug=False):
    """
    Check for subspace trail and MDS property of matrix M.
    """
    sub_len, sub_dim = getLengthSubspaceTrail(F, M, t)
    
    if debug:
        print(M)
        print(f"Subspace: len={sub_len}, dim={sub_dim}")
    
    is_ok = sub_len == t-1
    
    if need_mds:
        is_mds = isAllInvertible(M, t)
        if debug:
            print(f"MDS: mds={is_mds}")
        is_ok = is_ok and is_mds
    
    if need_inv:
        is_inv = M.is_invertible()
        if debug:
            print(f"INV: inv={is_inv}")
        is_ok = is_ok and is_inv

    return is_ok


# -------------------------------------------------------------------------------------------
# HADES Design Strategy
# -------------------------------------------------------------------------------------------
class Hades:
    def __init__(self, name="Hades", F=None, t=None, rF=None, rf=None, rP=None, alpha=None, Minit=None, MF=None, MP=None, rcons=None, optRcons=False):
        """
        Initialize a HADES instance.

        Args:
        - name (str): Name of the concrete HADES design.
        - p (int): Prime characteristic for the field.
        - n (int): Degree of field extension.
        - ipoly (str, optional): Irreducible polynomial for the field (if n > 1).
        - t (int): State size.
        - rF (int): Number of full (external) rounds.
        - rf (int): Number of initial full (external) rounds.
        - rP (int): Number of partial (internal) rounds.
        - alpha (int): Power map exponent for the S-box.
        - Minit (matrix): Initial matrix for the cipher.
        - MF (matrix): Matrix for full (external) rounds.
        - MP (matrix): Matrix for partial (internal) rounds.
        - rcons (list of field elements): Round constants.
        - optRcons (bool): Only add roundconstants before S-boxes.
        """
        self.name = name
        
        # Initializing field
        self.p = F.characteristic()
        self.n = F.degree()
        self.F = F

        if gcd(self.p**self.n - 1,alpha) != 1:
            raise ValueError(f"Invalid powermap exponent (alpha)")
        
        # State size and round numbers
        self.t = t
        self.rF = rF
        self.rf = rF // 2 if rf is None else rf # Default is same number of full rounds at beginning and end 
        self.rf_ = rF - self.rf # Remaining full rounds
        self.rP = rP
        self.R = self.rF + self.rP # Total number of rounds
        
        # Exponent for S-box monomial
        self.alpha = alpha
        self.alpha_inv = inverse_mod(alpha, self.p**self.n - 1)
        self.Sbox = lambda x : x**self.alpha
        self.Sbox_inv = lambda x : x**self.alpha_inv

        # Small helpers
        self.int_to_field   = lambda x : self.F.from_integer(x)
        self.field_to_int = lambda x : x.to_integer() if F.degree() > 1 else ZZ(x)
        self.hex_to_field   = lambda x : self.int_to_field(int(x, 16))
        self.field_to_hex = lambda x : hex(self.field_to_int(x))[2:]
        
        self.bit_length = self.n * ceil(log(self.p,2))  # bits reserved for representation of field element
        self.hex_length = int(ceil(self.n / 4))

        self.is_full_round = lambda r : r < self.rf or r >= self.rf + self.rP
        
        # Round constants (rcons), given as list
        if isinstance(rcons, list) and len(rcons) >= t * self.R and all([c in self.F for c in rcons]):
            rcons = [rcons[t * i : t * (i+1)] for i in range(self.R)]
            if optRcons: # Only add roundconstants before S-boxes
                for r in range(self.R):
                    if not self.is_full_round(r):
                        for i in range(1, t):
                            rcons[r][i] = self.F(0)
            self.rcons = [vector(self.F, c) for c in rcons]
        else:
            raise ValueError(f"Invalid round constants (rcons)")
        
        # Initial matrix (Minit), given as list of lists
        if Minit.dimensions() == (self.t,self.t) and Minit.parent().base() == self.F:
            self.Minit = Minit
            self.Minit_inv = self.Minit.inverse()
        else:
            raise ValueError(f"Invalid initial matrix (Minit)")

        # Full (external) rounds matrix (MF), given as list of lists
        if MF.dimensions() == (self.t,self.t) and MF.parent().base() == self.F:
            self.MF = MF
            self.MF_inv = self.MF.inverse()
        else:
            raise ValueError(f"Invalid external rounds matrix (MF)")

        # Partial (internal) rounds matrix (MI), given as list of lists
        if MP.dimensions() == (self.t,self.t) and MP.parent().base() == self.F:
            self.MP = MP
            self.MP_inv = self.MP.inverse()
        else:
            raise ValueError(f"Invalid internal rounds matrix (MP)")

    # ----------------------------------------------------------------------
    # Helper functions
    # ----------------------------------------------------------------------
    def print_words_to_hex(self, state):
        """Print the state as a list of hexadecimal strings."""
        print(["{0:#0{1}x}".format(self.field_to_int(entry), self.hex_length + 2) for entry in state.list()])

    def __str__(self):
        """Return a string representation of the HADES instance."""
        result = f"{self.name.upper()} instance over GF({self.p:d}^{self.n:d}), t={self.t:d}, alpha={self.alpha}; "
        result += f"rF={self.rF:d}={self.rf}+{self.rf_}, rP={self.rP:d}"
        return result
        
    def set_rounds(self, rF=None, rP=None, rf=None):
        """Reset the number of rounds for the cipher."""
        if rF is None:
            rF = self.rF 
        if rP is None:
            rP = self.rP
        if rF + rP > len(self.rcons):
            raise ValueError(f"Invalid round numbers (rF,rf,rP)")

        self.rF = rF
        self.rf = rF // 2 if rf is None else rf # Default is same number of full rounds at beginning and end 
        self.rf_ = rF - self.rf # Remaining full rounds
        self.rP = rP
        self.R = self.rF + self.rP # Total number of rounds

    # ----------------------------------------------------------------------
    # Components
    # ----------------------------------------------------------------------
    
    def AddRoundCons(self, x, r, inv=False):
        """
        Add or subtract round constants from the state.

        Args:
        - x (vector): The state vector.
        - r (int): Round number.
        - inv (bool): Whether to apply inverse operation.
        """
        return x - self.rcons[r] if inv else x + self.rcons[r]

    def SubWordsRF(self, x, inv=False):
        """
        Apply or invert the S-box for all branches in full (external) rounds.

        Args:
        - x (vector): The state vector.
        - inv (bool): Whether to apply inverse operation.
        """
        # apply_map returns a copy, original left unchanged
        return x.apply_map(self.Sbox_inv) if inv else x.apply_map(self.Sbox) 
        
    def SubWordsRP(self, x, inv=False):
        """
        Apply or invert the S-box for branch 0 in partial (internal) rounds.

        Args:
        - x (vector): The state vector.
        - inv (bool): Whether to apply inverse operation.
        """
        x_ = copy(x)
        x_[0] = self.Sbox_inv(x[0]) if inv else self.Sbox(x[0]) # Apply (inverse) S-box to branch 0 only
        return x_
    
    def RoundFull(self, x, r, inv=False):
        """
        Perform a single full (external) round of the cipher.

        Args:
        - x (vector): The state vector.
        - r (int): Round number.
        - inv (bool): Whether to apply inverse operation.
        """
        if inv:
            x = self.MF_inv * x
            x = self.SubWordsRF(x, inv)
            x = self.AddRoundCons(x, r, inv)
        else:
            x = self.AddRoundCons(x, r, inv)
            x = self.SubWordsRF(x, inv)
            x = self.MF * x
        return x
    
    def RoundPartial(self, x, r, inv=False):
        """
        Perform a single partial (internal) round of the cipher.

        Args:
        - x (vector): The state vector.
        - r (int): Round number.
        - inv (bool): Whether to apply inverse operation.
        """
        if inv:
            x = self.MP_inv * x
            x = self.SubWordsRP(x, inv)
            x = self.AddRoundCons(x, r, inv)
        else:
            x = self.AddRoundCons(x, r, inv)
            x = self.SubWordsRP(x, inv)
            x = self.MP * x
        return x
    
    # ----------------------------------------------------------------------
    # Evaluation
    # ----------------------------------------------------------------------
    def eval_with_intermediate_values(self, x, inv=False, rstart=None, rend=None):
        """
        Evaluate the cipher with intermediate values recorded.

        Args:
        - x (list or vector): Input state.
        - inv (bool): Whether to apply inverse operation.
        - rstart (int, optional): Starting round.
        - rend (int, optinal): Ending round.
        """
        if len(x) != self.t:
            raise ValueError(f"Invalid input of size {len(x)} for permutation with statesize {self.t}.")
        x = vector(x)
        result = [x]
        
        # One could start at arbitrary round and go forward or backward
        rstart = 0 if rstart is None else rstart
        rend = self.R if rend is None else rend
        if rstart == rend:
            return result
            
        rounds = range(rstart, rend)[::-1] if inv else range(rstart, rend)
        
        if not inv and rstart == 0:
            x = self.Minit * x
            result.append(x)
            
        for r in rounds:
            if r < self.rf or r >= self.rf + self.rP:  # Full (external) rounds
                x = self.RoundFull(x, r, inv)
            else:  # Partial (internal) rounds
                x = self.RoundPartial(x, r, inv)
            result.append(x)
        
        if inv and rstart == 0:
            x = self.Minit_inv * x
            result.append(x)

        return result

    def __call__(self, x, inv=False, rstart=None, rend=None):
        """
        Evaluate the cipher on the input state.

        Args:
        - x (list or vector): Input state.
        - inv (bool): Whether to apply inverse operation.
        - rstart (int, optional): Starting round.
        - rend (int, optional): Ending round.
        """
        return self.eval_with_intermediate_values(x, inv, rstart, rend)[-1]

# -------------------------------------------------------------------------------------------
# POSEIDON2b Permutation
# -------------------------------------------------------------------------------------------
class Poseidon2b(Hades):
    name = "poseidon2b"
    
    def __init__(self, n=None, ipoly=None, t=None, rF=None, rP=None, alpha=None, MF=None, MP=None, rcons=None, instance=None, kappa=None, toy=False):
        """
        Initialize a POSEIDON instance with cryptographic parameters.

        HADES arguments:
        - name (str): Name of the concrete HADES design.
        - n (int): Degree of field extension.
        - ipoly (str, optional): Irreducible polynomial for the field (if n > 1).
        - t (int): State size.
        - rF (int): Number of full (external) rounds.
        - rP (int): Number of partial (internal) rounds.
        - alpha (int): Power map exponent for the S-box.
        - MF (list of lists): Matrix for full (external) rounds.
        - MP (list of lists): Matrix for partial (internal) rounds.
        - rcons (list of field elements): Round constants.
        Additional arguments:
        - instance (str, optional): File to parse parameters from.
        - kappa (int, optional): Security parameter.
        """
            
        # Parse parameters from file
        if instance is not None:
            if instance.endswith('sobj'): # Parse parameters from dict
                raise NotImplementedError("Parsing from sobj file not implemented for Poseidon2b")
            else:
                raise ValueError("Unsupported instance type.")
        
        # Valid Poseidon2b instances or Toy version
        if not toy and (n,t) not in [(32,16),(32,24),(64,8),(64,12),(128,4),(128,6)]:
            raise ValueError(f"Invalid Poseidon2b instance (n,t)=({n},{t})")
        
        # Field
        if n <= 2:
            raise ValueError(f"Invalid field degree n={n}")
        F = GF(2**n, name='X') if ipoly is None else GF(2**n, name='X', modulus=ipoly)

        # Partial (internal) matrix MP: Matrix with only ones, except diagonal
        if MP is None:
            MP = self.generate_MP(F=F, t=t)
            # check_MP(F, M, t, need_mds=False, debug=False)
        
        # Full (external) matrix MF: MDS for t=3,4 and it has branch number t'+4 for t >= 8
        if MF is None:
            if t in [2,3]:
                MF = MP # For toy versions with t=2,3, we set MF = MP, where MP is additionally MDS
            else:
                MF = self.generate_MF(F=F, t=t)

        # Round constants
        if rcons is None:
            rcons = self.generate_rcons(SHAKE_INIT="Poseidon2b", n=n, t=t, r=rF+rP)
            rcons = [F.from_integer(c) for i, c in enumerate(rcons)]  # Convert to field elements

        Hades.__init__(self, name=Poseidon2b.name.capitalize(), F=F, t=t, rF=rF, rf=rF//2, rP=rP, alpha=alpha, Minit=MF, MF=MF, MP=MP, rcons=rcons, optRcons=True)

    # ----------------------------------------------------------------------
    # Helper functions
    # ----------------------------------------------------------------------
    def generate_MP(self, F, t):
        # Partial (internal) matrix MP for Poseidon2b
        # Diagonal is chosen such that (1) MP is invertible and (2) MP admits no arbitrarily long subspace trails.

        X = F.gens()[0]
        ones = Matrix.ones(F, t) - Matrix.identity(F, t)

        # Fixed matrix for Poseidon2b instances
        if F.degree() == 32 and t == 16:
            return ones + Matrix.diagonal(F, [X**10, X**3, X**8, X**11, X**14, 1, X**15, X**10 + 1, X**4, X**2 + 1, X**6, X**7, X**13 + 1, X**2, X**5, X + 1])
        if F.degree() == 32 and t == 24:
            return ones + Matrix.diagonal(F, [X**11 + X**7 + 1, X**14 + X**5, X**15 + X**8, X**15 + X**5, X**12 + X**3, X**14 + X**3, X**10 + X, X**8 + X**3, X**14 + 1, X**5 + 1, X**12 + X**4, X**5 + X**4, X**12 + X**11, X**6 + X**3, X**12 + X**5, X**9 + X**3, X**8 + X**5, X**15 + X**10, X**11 + X**7, X + 1, X**13 + X, X**7 + X**5, X**12 + X**2, X**15 + X**9])
        if F.degree() == 64 and t == 8:
            return ones + Matrix.diagonal(F, [X**7 + 1, X, X**9, X**7, X**13, X**12, X**14, X**6])
        if F.degree() == 64 and t == 12:
            return ones + Matrix.diagonal(F, [X + 1, X**3, X**7, X**13, X**15, 1, X**15 + 1, X**11, X, X**10 + 1, X**12, X**10])
        if F.degree() == 128 and t == 4:
            return ones + Matrix.diagonal(F, [X**5, X**13, X**9, X**11])
        if F.degree() == 128 and t == 6:
            return ones + Matrix.diagonal(F, [X**8, X**10, X**3, X**2, X**11, X**14])

        # Generate suitable matrix for other instances (for toy versions)
        shake_utils = ShakeUtils(init_shake="MI-Poseidon2b", p=F.characteristic(), n=F.degree())
        shake_reader = shake_utils.init_shake_reader()
        is_ok = False
        while not is_ok:
            # M = ones + Matrix.diagonal(F, [F.random_element() for _ in range(t)])
            M = ones + Matrix.diagonal(F, [F.from_integer(c) for c in shake_utils.get_random_elements(t, shake_reader)])
            is_ok = check_MP(F, M, t, need_mds=(t in [2,3]), need_inv=True) # MP has to be MDS if t=2,3
        return M
    
    def generate_MF(self, F, t):
        # Full (external) matrix MF for Poseidon2b
        X = F.gens()[0]
        M4 = Matrix(F,[[X**2 + 1, X**2 + X + 1, 1, X + 1], [X**2, X**2 + X, 1, 1], [1, X + 1, X**2 + 1, X**2 + X + 1], [1, 1, X**2, X**2 + X]]) # 4x4 MDS matrix
        if t == 4:
            return M4
        elif t == 6:
            return Matrix.circulant([X**9, 1, X**11, X, X, 1]).transpose()
        else:
            t_ = t//4
            blocks = [[X*M4 if i == j else M4 for j in range(t_)] for i in range(t_)]
            return block_matrix(blocks, subdivide=False)
    
    def generate_rcons(self, SHAKE_INIT, n, t, r):
        # Initialize ShakeUtils with adjustable INIT_SHAKE
        shake_utils = ShakeUtils(init_shake=SHAKE_INIT, p=2, n=n)
        shake_reader = shake_utils.init_shake_reader()
        return shake_utils.get_random_elements(t * r, shake_reader)