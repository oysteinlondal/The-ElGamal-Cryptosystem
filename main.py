import secrets
import sympy
import math
import time

# Initialize systemRandom class from secrets module
secretsGenerator = secrets.SystemRandom()


# Transforms integer into odd number by
# removing all factors of 2
def rem_powers_of_two(n):
    r = n
    while r % 2 == 0:
        r = r // 2
    return r


# Pollard's rho algorithm for prime factorization
# Optimal for finding prime factors of integers with small factors
# If the factors are too big, it is very slow
# Therefore, this algorithm is not optimal for ElGamal since
# the prime p needs to have big factors so that the discrete logarithm
# problem is computationally hard.
def pollard_rho(m):
    factors = []
    c = 1
    modulus = m
    while 1:
        x = 2
        y = 2
        d = 1
        f = lambda x: (x ** 2 + c) % modulus
        while d == 1:
            x = f(x)
            y = f(f(y))
            d = math.gcd(abs(x - y), modulus)
        # Check if finding a prime factor failed
        # Sometimes Pollard's rho returns a non-prime number
        # When this happens we try again
        if d == modulus or not is_prime(d):
            # Try again with higher value of c
            c += 1
            continue
        factors.append(d)
        e = modulus // d
        # If e is prime we do not need to factor anymore
        if is_prime(e):
            factors.append(e)
            return factors
        # If e is not prime we have to start over with a new modulus in order to factor e as well
        modulus = e


# Uses Pollard's rho to factor an integer into
# it's prime factors
def prime_factorization(n):
    # Remove power of 2
    # Pollard Rho can't factor even numbers
    r = rem_powers_of_two(n)
    prime_factors = []
    if r < n:
        prime_factors.append(2)
    if is_prime(r):
        prime_factors.append(r)
        return prime_factors
    # Find all prime factors
    prime_factors += pollard_rho(r)
    # Add 2 as a factor if n contained any power of 2
    return prime_factors


def find_generator_of_general_prime(n):
    # Pollard's rho
    all_prime_factors = list(set(prime_factorization(n)))
    print(all_prime_factors)
    b = 1
    while 1:
        a = secretsGenerator.randint(1, n - 1)
        for i in range(0, len(all_prime_factors)):
            # Modulus is n + 1 = p
            b = modular_exponentiation(a, n // all_prime_factors[i], n + 1)
            if b == 1:
                break
        if b != 1:
            return a


# Represents number as a sequence of bits
def binary_representation(number):
    binary = bin(number)[2:]
    return binary


# Effective modulo computation for integers with large exponents
def modular_exponentiation(base, exponent, modulus):
    bin_exp = binary_representation(exponent)
    x = 1
    power = base % modulus
    for i in reversed(range(0, len(bin_exp))):
        if bin_exp[i] == '1':
            x = (x * power) % modulus
        power = (power * power) % modulus
    return x


# Miller-Rabin probabilistic primality test
def is_prime(n, t=3):
    # 0 is never prime!
    if n == 0:
        return False
    # 1, 2 and 3 are primes
    # No need to test these
    if n <= 3:
        return True
    # A prime is never even!
    if n % 2 == 0:
        return False
    # Need to find s and odd number r so that n = 2^s * r
    s = 0
    r = n - 1
    while r % 2 == 0:
        r = r // 2
        s = s + 1
    # If False n is composite
    # If True n is prime
    for i in range(1, t):
        a = secretsGenerator.randint(2, n - 2)
        y = modular_exponentiation(a, r, n)
        if y != 1 and y != (n - 1):
            j = 1
            while j <= (s - 1) and y != (n - 1):
                y = y ** 2 % n
                if y == 1:
                    return False
                j = j + 1
            if y != (n - 1):
                return False
    return True


# Generates a list of all primes between 3 and 1000
primes = list(sympy.primerange(3, 1000))


# Checks if a integer has any small prime factors
# This is more optimal than to use an computationally
# expensive primality test for such small factors
def small_factors(q):
    # q has a factor of small prime s if q mod s = 0.
    # Ex. 105 mod 5 = 0, 105 mod 3 = 0 and 105 mod 7 = 0.
    # Hence 105 is not a prime.
    # p has a factor of small prime s if q mod s = (s - 1)/2.
    # Ex. 103 mod 23 = (23 - 1)/2 = 11, then p = 2*103 + 1 = 207.
    # Since 207 = 3 * 3 * 23, p = 207 is not prime.
    # Note that one of the prime factors is 23, which
    # corresponds to s.
    for s in primes:
        if (q % s == 0) or (q % s == (s - 1) // 2):
            return True
    return False


# Computes k-bit safe prime
# These are primes of the form 2q + 1 where
# q is a also a prime. q is then a Sophie Germain prime.
# k >= 1024 minimum requirement as of 2020.
# 2048-bits recommended, but is slow to generate!
def find_safe_prime(k):
    while 1:
        q = secrets.randbits(k - 1)
        # Even numbers cannot be prime
        if q % 2 == 0:
            continue
        # Optimizes performance for large integers by checking for small factors first
        # Primes have no factors other than itself and 1
        if q > 1000 and small_factors(q):
            continue
        # q needs to be prime
        if not is_prime(q):
            continue
        p = 2 * q + 1
        # p needs to be prime
        if is_prime(p):
            return p


# The process of finding the primitive root of a safe prime
# is significantly more simple than for an arbitrary one
# This speeds up the cryptosystem by a lot!
def find_generator_of_safe_prime(p):
    # The following is ONLY possible if p is a safe prime!
    # Number greater than 1, but less than p - 1
    for g in range(2, p - 2):
        a = modular_exponentiation(g, (p - 1) // 2, p)
        # The smallest primitive root is returned
        # This does not affect the security, and makes the
        # ElGamal implementation more efficient
        if a != 1:
            return g


# Only Alice has access to this dictionary!
# Should be protected from the public
protected_parameters = {
    "private_key": 0,
    "generator": 0,
    "prime": 0
}


# Generating prime, generator and first private and public key
def key_generation(k_bits):
    # Set start point
    start_time = time.time()
    print("--- Generating safe prime of %s bits ---" % k_bits)
    safe_prime = find_safe_prime(k_bits)
    # Store parameter for later
    protected_parameters["prime"] = safe_prime
    print("Generated safe prime: %s" % safe_prime)
    # Calculate total computation time
    print("--- Safe prime generated in %s seconds ---" % (time.time() - start_time))
    generator = find_generator_of_safe_prime(safe_prime)
    # Store parameter for later
    protected_parameters["generator"] = generator
    print("Generator to be used: %s" % generator)
    print("Generating private key ...")
    # Using module secrets to increase randomness
    private_a = secretsGenerator.randint(0, safe_prime - 2)
    # Store parameter for later
    protected_parameters["private_key"] = private_a
    print("Computing public sub-key ...")
    public_sub_a = modular_exponentiation(generator, private_a, safe_prime)
    print("Public sub-key is: %s" % public_sub_a)
    public_key = {
        "prime": safe_prime,
        "generator": generator,
        "sub-key": public_sub_a
    }
    print("--- Sending public key: (%s, %s, %s) ---" % (safe_prime, generator, public_sub_a))
    return public_key


# Encoding maps a message block
# to an integer in the range [0, ..., 1114111]
# depending on if special characters are used.
# If the safe prime is less than this max value
# an incorrect decoding might happen (if some special characters are used)
def encode(message_string):
    encoded_string = []
    for char in message_string:
        encoded_string.append(ord(char))
    return encoded_string


def decode(message_integer):
    decoded_string = ""
    for integer in message_integer:
        decoded_string += chr(integer)
    return decoded_string


# Encrypting the chosen message
def encrypt(message_string, received_public_key):
    print("Public key received")
    print("Encoding message ...")
    encoded_string = encode(message_string)
    C = []
    P = []
    print("Encrypting message ...")
    start_time = time.time()
    for m_i in encoded_string:
        k_i = secretsGenerator.randint(0, received_public_key["prime"])
        public_sub_i = modular_exponentiation(received_public_key["generator"], k_i, received_public_key["prime"])
        c_i = m_i * modular_exponentiation(received_public_key["sub-key"], k_i, received_public_key["prime"])
        C.append(c_i)
        P.append(public_sub_i)
    print("--- Message encrypted in %s seconds ---" % (time.time() - start_time))
    public_key = {
        "ciphertext": C,
        "sub-keys": P
    }
    print("Sending public key: (%s, %s) ..." % (C, P))
    return public_key


# Decrypting the received message
def decrypt(received_public_key):
    print("Public key received")
    decrypted = []
    print("Decrypting message ...")
    start_time = time.time()
    for i in range(0, len(received_public_key["sub-keys"])):
        shared_key_i = modular_exponentiation(received_public_key["sub-keys"][i], protected_parameters["prime"] - 1 - protected_parameters["private_key"], protected_parameters["prime"])
        m_i = shared_key_i * received_public_key["ciphertext"][i] % protected_parameters["prime"]
        decrypted.append(m_i)
    print("--- Message decrypted in %s seconds ---" % (time.time() - start_time))
    print("Decoding message ...")
    decoded_message = decode(decrypted)
    return decoded_message


# bits = 1024 approx. 30 seconds
# bits = 2048 approx. 300 seconds
bits = int(input("Specify size of safe prime in bits (>= 1024 recommended): "))
# If k-bits is too low, try again
while bits <= 2:
    print("No safe prime of this size!")
    bits = int(input("Specify size of safe prime in bits: "))
# Decoding and encoding constructed in a way that makes
# incorrect mapping for small primes. Using bits > 20 should fix this in most cases.
if bits < 21:
    print("Warning! Message might not be decoded properly using this bit-size.")
# Generating first public key
public_key_a = key_generation(bits)
while 1:
    message = input("Type in message to be sent: ")
    public_key_b = encrypt(message, public_key_a)
    decrypted_message = decrypt(public_key_b)
    print("Decrypted message is: %s" % decrypted_message)
    user_prompt = input("Do you want to send more messages? (y/n) ")
    if user_prompt == 'n':
        break
    elif user_prompt != 'y':
        print("Unknown value!")
        break
