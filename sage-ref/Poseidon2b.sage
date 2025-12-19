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
    
    def __init__(self, n=None, ipoly=None, t=None, rF=None, rP=None, alpha=None, MF=None, MP=None, rcons=None, toy=False):
        """
        Initialize a POSEIDON2b instance with cryptographic parameters.

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
        """
        
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
        if t == 4: # MDS matrix
            return M4
        elif t == 6: # circulant MDS matrix
            return Matrix.circulant([X**9, 1, X, X, X**11, 1])
        else: # Non-MDS matrix (with branch number 4 + t/4) for t=8,12,16,24
            t_ = t//4
            blocks = [[X*M4 if i == j else M4 for j in range(t_)] for i in range(t_)]
            return block_matrix(blocks, subdivide=False)
    
    def generate_rcons(self, SHAKE_INIT, n, t, r):
        # Initialize ShakeUtils with adjustable INIT_SHAKE
        shake_utils = ShakeUtils(init_shake=SHAKE_INIT, p=2, n=n)
        shake_reader = shake_utils.init_shake_reader()
        return shake_utils.get_random_elements(t * r, shake_reader)


# -------------------------------------------------------------------------------------------
# POSEIDONb Permutation
# -------------------------------------------------------------------------------------------
class Poseidonb(Hades):
    name = "poseidonb"
    
    def __init__(self, n=None, ipoly=None, t=None, rF=None, rP=None, alpha=None, MF=None, MP=None, rcons=None, toy=False):
        """
        Initialize a POSEIDONb instance with cryptographic parameters.

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
        """
        
        # Valid Poseidonb instances or Toy version
        if not toy and (n,t) not in [(32,16),(32,24),(64,8),(64,12),(128,4),(128,6)]:
            raise ValueError(f"Invalid Poseidonb instance (n,t)=({n},{t})")
        
        # Field
        if n <= 2:
            raise ValueError(f"Invalid field degree n={n}")
        F = GF(2**n, name='X') if ipoly is None else GF(2**n, name='X', modulus=ipoly)

        # Partial (internal) matrix MP: Matrix with only ones, except diagonal
        if MP is None:
            MP = self.generate_MP(F=F, t=t)
            # check_MP(F, M, t, need_mds=False, debug=False)
        
        # Full (external) matrix MF: MDS for all instances
        if MF is None:
            if t in [2,3]:
                MF = MP # For toy versions with t=2,3, we set MF = MP, where MP is additionally MDS
            else:
                MF = self.generate_MF(F=F, t=t)
        
        # Round constants
        if rcons is None:
            rcons = self.generate_rcons(SHAKE_INIT="Poseidonb", n=n, t=t, r=rF+rP)
            rcons = [F.from_integer(c) for i, c in enumerate(rcons)]  # Convert to field elements

        Hades.__init__(self, name=Poseidonb.name.capitalize(), F=F, t=t, rF=rF, rf=rF//2, rP=rP, alpha=alpha, Minit=MF, MF=MF, MP=MP, rcons=rcons, optRcons=True)

    # ----------------------------------------------------------------------
    # Helper functions
    # ----------------------------------------------------------------------
    def generate_MP(self, F, t):
        # Partial (internal) matrix MP for Poseidonb
        # Diagonal is chosen such that (1) MP is invertible and (2) MP admits no arbitrarily long subspace trails.

        X = F.gens()[0]
        ones = Matrix.ones(F, t) - Matrix.identity(F, t)

        # Fixed matrix for Poseidonb instances
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
        shake_utils = ShakeUtils(init_shake="MI-Poseidonb", p=F.characteristic(), n=F.degree())
        shake_reader = shake_utils.init_shake_reader()
        is_ok = False
        while not is_ok:
            # M = ones + Matrix.diagonal(F, [F.random_element() for _ in range(t)])
            M = ones + Matrix.diagonal(F, [F.from_integer(c) for c in shake_utils.get_random_elements(t, shake_reader)])
            is_ok = check_MP(F, M, t, need_mds=(t in [2,3]), need_inv=True) # MP has to be MDS if t=2,3
        return M
    
    def generate_MF(self, F, t):
        # Full (external) matrix MF for Poseidonb
        X = F.gens()[0]
        M4 = Matrix(F,[[X**2 + 1, X**2 + X + 1, 1, X + 1], [X**2, X**2 + X, 1, 1], [1, X + 1, X**2 + 1, X**2 + X + 1], [1, 1, X**2, X**2 + X]]) # 4x4 MDS matrix
        if t == 4: # MDS matrix
            return M4
        elif t == 6: # circulant MDS matrix
            return Matrix.circulant([X**9, 1, X, X, X**11, 1])
        else: # MDS Cauchy matrices for t=8,12,16,24
            # Generate from two pairwise distinct lists
            if F.degree() == 32 and t == 16:
                L1 = [F.from_integer(x) for x in [0x76c5949c, 0xad96148c, 0xd2e54c71, 0x3237cbcb, 0x14ec29d7, 0xed906839, 0x2db06739, 0xd6a65cc8, 0x158ffbc4, 0x24846fca, 0xec0c72c0, 0xee0c4dbe, 0xd176c64c, 0x5559c73a, 0x866efb11, 0x36dbc7d6]]
                L2 = [F.from_integer(x) for x in [0xf986f72a, 0xd81cf04b, 0x6d7c6b2a, 0x62749077, 0xb11d686d, 0x4cf78ae1, 0xf078f403, 0xe47eafd6, 0x0a4e583c, 0x8f5b97c9, 0x02b4efb0, 0x8bb61c29, 0x82250395, 0xc332e43f, 0xc64684ca, 0x8a47bbb7]]
            if F.degree() == 32 and t == 24:
                L1 = [F.from_integer(x) for x in [0x0760a613, 0xe090882d, 0x2ae85a8a, 0x0731d180, 0x39be5fb9, 0x1a7ab25d, 0xed0502f2, 0xcf7ee3e5, 0x0638f392, 0xcc420be2, 0x85e20ac2, 0xa437419c, 0xee81445f, 0xac43182d, 0xf6b138c3, 0x46fa8910, 0x921da5f5, 0x0807fa2d, 0xa9f0bd0d, 0x7ecbab68, 0x8eadc645, 0xdfe5ea35, 0xd54c85cd, 0x7411f8b0]]
                L2 = [F.from_integer(x) for x in [0x20639c59, 0xa76c4447, 0x7cb87735, 0xa9732ef0, 0x345aa9fb, 0x11588cdb, 0xe135fb88, 0xf09c93e8, 0x7ded2373, 0x79f4d7fc, 0xf4ee6b8a, 0x60561c3f, 0xec6053d3, 0x592f2e78, 0x081b935e, 0xbd2920eb, 0x6531043c, 0x0a2aa330, 0xea890bf4, 0xf30ce395, 0x0dd9499a, 0x23ed0b85, 0x8dcf1ed2, 0xf0534819]]
            if F.degree() == 64 and t == 8:
                L1 = [F.from_integer(x) for x in [0xe2a5b6b9ba860de5, 0x6f8ac9feb39919b2, 0x1c2616e746c82ca2, 0xe78ca93dc5706ce8, 0x871304bbc6683095, 0x06a1b3f93397ba20, 0xfefb53fc36e3ce0a, 0x8b083c3871cde7c6]]
                L2 = [F.from_integer(x) for x in [0x7a308f3c64629cca, 0x732c493862a6ce3a, 0x639208c08fb4fc08, 0x0e21643692f331ba, 0x9c42022a91085132, 0x24233dad8120b794, 0xadb86f790d52e1a3, 0x3e2feedd7cb5c125]]
            if F.degree() == 64 and t == 12:
                L1 = [F.from_integer(x) for x in [0x2c2be52b45769690, 0x6c6c85f8ec69a0aa, 0x370e7c9564dba398, 0x0d92b0f1bb01b63d, 0x42deed41bb5a7ebc, 0x8f151ed5a1b7ad79, 0x2550bc26916ee14f, 0x4fd19a47de09b6ac, 0x43defa828260c742, 0xf138384f0a53000a, 0xe1dbd9c8fb4aae4b, 0xabbfafa8c6cf04bd]]
                L2 = [F.from_integer(x) for x in [0xf35f7271fabf3988, 0x53758343de351a5c, 0xb94f30de34035c68, 0x5e65735b3e0bf625, 0x13357b63f136713a, 0x776924c4b74d2cd8, 0xa8464e93bc1e44ec, 0x91ae7f13e2cc927f, 0xf0c9ee8ccf2285b8, 0x7bb2a840a4824715, 0xb55c96024c7b872f, 0xd95a35290ced7fd0]]
            assert(len(L1) == t and len(L2) == t)
            return Matrix(F,[[(L1[i] - L2[j])**(-1) for j in range(t)] for i in range(t)]) 
    
    def generate_rcons(self, SHAKE_INIT, n, t, r):
        # Initialize ShakeUtils with adjustable INIT_SHAKE
        shake_utils = ShakeUtils(init_shake=SHAKE_INIT, p=2, n=n)
        shake_reader = shake_utils.init_shake_reader()
        return shake_utils.get_random_elements(t * r, shake_reader)