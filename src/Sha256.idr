module Sha256

import Data.Bin
import Data.Vect
import Debug.Trace
import Decidable.Equality
import Numbers

-- heavily borrowed from https://rosettacode.org/wiki/Category:FunL
public export
interface HasLength a where
  get_len : a -> Nat

public export
implementation HasLength (Vect l e) where
  get_len a = length a

public export
interface ContainsBytes a where
  get_byte : a -> Nat -> Integer

vectLengthIsL : {ll : Nat} -> (v : Vect ll x) -> length v = ll
vectLengthIsL Vect.Nil = Refl
vectLengthIsL (Vect.(::) _ rest) =
  rewrite vectLengthIsL rest in
  Refl

ifVectLenIsSLThenPredVectLenIsL : {ll : Nat} -> (v : Vect (S ll) x) -> pred (length v) = ll
ifVectLenIsSLThenPredVectLenIsL v =
  rewrite vectLengthIsL v in
  Refl

public export
implementation ContainsBytes (Vect (S l) Integer) where
   get_byte a n =
     let
       lastElementOf : Nat
       lastElementOf = pred (length a)

       indexIntoVect : Fin (S l)
       indexIntoVect =
         rewrite sym (ifVectLenIsSLThenPredVectLenIsL a) in
         restrict lastElementOf (cast n)
     in
     index indexIntoVect a

byte_off : Nat -> Nat
byte_off Z = 1
byte_off (S v) = byte_off v

padding_val : {l : Nat} -> Nat -> Fin l -> Nat -> Nat
padding_val val i x = trunc 8 (shr (byte_off (finToNat i)) val)

int_padding : (len_bytes : Nat) -> Nat -> Vect len_bytes Nat
int_padding len_bytes val = replicate len_bytes 0

short_at : (Add n, Shl n, FromInteger n, HasLength a, ContainsBytes a) => a -> Nat -> n
short_at message idx = add (shl 8 (fromInteger (get_byte message idx))) (fromInteger (get_byte message (add idx 1)))

int_at : (Add n, Shl n, FromInteger n, HasLength a, ContainsBytes a) => a -> Nat -> n
int_at message idx = add (shl 16 (short_at message idx)) (short_at message (add idx 2))

plusN1EqSn : (n : Nat) -> plus n 1 = S n
plusN1EqSn Z = Refl
plusN1EqSn (S n) =
  rewrite plusN1EqSn n in
  Refl

range : (n : Nat) -> Vect n Nat
range Z = Vect.Nil
range (S n) =
  rewrite sym (plusN1EqSn n) in
  range n ++ Vect.(::) n Vect.Nil

build_int_vector : (Add n, FromNat n, ToNat n, FromInteger n, Shl n, HasLength a, ContainsBytes a) => (message : a) -> Vect (shr (get_len message) 2) n
build_int_vector message =
  let
    r : Vect (shr (get_len message) 2) n
    r = map fromNat $ range (shr (get_len message) 2)
  in
  map (\i => int_at message (fourI i)) r
  where
    fourI : n -> Nat
    fourI n = toNat $ shl 2 n

rotateright : (Add n, Shr n, Shl n) => n -> Nat -> Nat -> n
rotateright v count_unconstrained total_bits =
  let
    count : Nat
    count = natMod count_unconstrained total_bits
  in
  add (shr count v) (shl (natSub total_bits count) v)

extend_48_word : (Eq n, Gt n, Add n, Xor n, FromNat n, Shr n, Shl n, Trunc n, Bitlist n) => Vect 64 n -> Fin 64 -> n
extend_48_word w idx =
  if 16 > finToNat idx then
    index idx w
  else
    compute_synth w idx

  where
    compute_synth : Vect 64 n -> Fin 64 -> n
    compute_synth w idx =
      let
        widx_m_16 : Fin 64
        widx_m_16 = restrict 63 (cast (natSub (finToNat idx) 16))

        widx_m_15 : Fin 64
        widx_m_15 = restrict 63 (cast (natSub (finToNat idx) 15))

        widx_m_7 : Fin 64
        widx_m_7 = restrict 63 (cast (natSub (finToNat idx) 7))

        widx_m_2 : Fin 64
        widx_m_2 = restrict 63 (cast (natSub (finToNat idx) 2))

        w_m_16 : n
        w_m_16 = index widx_m_16 w

        w_m_15 : n
        w_m_15 = index widx_m_15 w

        w_m_7 : n
        w_m_7 = index widx_m_7 w

        w_m_2 : n
        w_m_2 = index widx_m_2 w

        s0 : n
        s0 = xor (rotateright w_m_15 7 32) (xor (rotateright w_m_15 18 32) (shr 3 w_m_15))

        s1 : n
        s1 = xor (rotateright w_m_2 17 32) (xor (rotateright w_m_2 19 32) (shr 10 w_m_2))
      in
      add w_m_16 (add s0 (add w_m_7 s1))

extend_48_words : (Eq n, Gt n, Xor n, Add n, Shl n, Shr n, Trunc n, FromNat n, Bitlist n) => Vect 16 n -> Vect 64 n
extend_48_words w =
  let
    extended_vec = w ++ (replicate 48 (fromNat 0))
  in
  map (\idx => extend_48_word extended_vec (restrict 63 (cast idx))) (range 64)

record Registers n where
  constructor MkRegisters

  a : n
  b : n
  c : n
  d : n
  e : n
  f : n
  g : n
  h : n

implementation (Show n) => Show (Registers n) where
  show r =
    "(MkRegisters " ++
      (show (a r)) ++ " " ++
      (show (b r)) ++ " " ++
      (show (c r)) ++ " " ++
      (show (d r)) ++ " " ++
      (show (e r)) ++ " " ++
      (show (f r)) ++ " " ++
      (show (g r)) ++ " " ++
      (show (h r)) ++ ")"

word_chunk : (Show n, Add n, Shl n, FromInteger n, HasLength aa, ContainsBytes aa) => aa -> Nat -> Vect 16 n
word_chunk message n =
  let
    n16 : Nat
    n16 = 16 * n
  in
  map
    (\idx =>
      let num = int_at message (n16 + idx) in
      trace (show num) num
    ) (range 16)

word_chunks : (Show n, Add n, Shl n, FromInteger n, FromNat n, HasLength aa, ContainsBytes aa) => aa -> List (Vect 16 n)
word_chunks message =
  let
    total_chunks : Nat
    total_chunks = shr 6 (get_len message)

    chunk_vect : Vect total_chunks (Vect 16 n)
    chunk_vect = map (word_chunk message) $ range total_chunks

    dummy_vec : Vect 16 n
    dummy_vec = trace (show chunk_vect) $ replicate 16 (fromNat 0)
  in
  map (\idx => index idx chunk_vect) $
    elemIndicesBy (\x,y => True) dummy_vec chunk_vect

record IdxRegisters n where
  constructor MkIdxRegisters

  idx : Nat
  reg : Registers n

implementation (Show n) => Show (IdxRegisters n) where
  show ir = "(MkIdxRegisters " ++ show (idx ir) ++ " " ++ show (reg ir) ++ ")"

transform_regs_i : (Show n, Eq n, Gt n, Add n, Xor n, And n, Invert n, FromNat n, Trunc n, Shl n, Shr n, Bitlist n) => Vect 64 n -> IdxRegisters n -> n -> IdxRegisters n
transform_regs_i k ir v =
  let
    i = idx ir
    r = reg ir

    s1 = xor (rotateright (e r) 6 32) (xor (rotateright (e r) 11 32) (rotateright (e r) 25 32))
    ch = xor (bitand (e r) (f r)) (bitand (invert 32 (e r)) (g r))
    temp1 = add (h r) (add s1 (add ch (add (index (restrict 63 (cast i)) k) v)))
    s0 = xor (rotateright (a r) 2 32) (xor (rotateright (a r) 13 32) (rotateright (a r) 22 32))
    maj = xor (bitand (a r) (b r)) (xor (bitand (a r) (c r)) (bitand (b r) (c r)))
    temp2 = add s0 maj

    newregs = MkRegisters (add temp1 temp2) (a r) (b r) (c r) (add (d r) temp1) (e r) (f r) (g r)
  in
  MkIdxRegisters (i + 1) $ trace (show newregs) newregs

transform_regs : (Show n, Eq n, Gt n, And n, Xor n, Invert n, Add n, Trunc n, Shl n, Shr n, FromNat n, Bitlist n) => Vect 64 n -> IdxRegisters n -> Vect 16 n -> IdxRegisters n
transform_regs k ir chunk = foldl (\ir,v => transform_regs_i k ir v) ir chunk

get_padded_size : Nat -> Nat
get_padded_size r =
  let
    rmod = natMod r 64
    rdown = natSub r rmod
  in
  if rmod == 0 || rmod >= 56 then
    rdown + 128
  else
    rdown + 64

record PaddedBits a where
  constructor MkPaddedBits

  old_data : a

implementation (HasLength aa) => HasLength (PaddedBits aa) where
  get_len message = get_padded_size (get_len message)

implementation (HasLength aa, ContainsBytes aa) => ContainsBytes (PaddedBits aa) where
  get_byte message n =
    let
      psize : Nat
      psize = get_padded_size (get_len message)

      padding_start : Nat
      padding_start = natSub psize 9

      byte_of_length : Nat
      byte_of_length = natSub (natSub psize padding_start) 1

      result : Integer
      result =
        if n == padding_start then
          0x80
        else if n > padding_start then
          let
            binval : Bin
            binval = trunc 8 (shr (8 * byte_of_length) (fromNat (get_len message)))
          in
          toInteger binval
        else if n < get_len (old_data message) then
          get_byte (old_data message) n
        else
          0
    in
    result

unpack_word : (Shr n, Trunc n) => n -> Vect 4 n
unpack_word n =
  let
    nlmid = shr 8 n
    nhmid = shr 8 nlmid
    nhigh = shr 8 nhmid
  in
  Vect.fromList
    [ trunc 8 nhigh
    , trunc 8 nhmid
    , trunc 8 nlmid
    , trunc 8 n
    ]

unp1 : unpack_word (nat2Bin 1000) = Vect.(::) (fromNat 0) (Vect.(::) (fromNat 0) (Vect.(::) (fromNat 3) (Vect.(::) (fromNat 0xe8) Vect.Nil)))
unp1 = Refl

unpack_hash : (Shr n, Trunc n) => Vect 8 n -> Vect 32 n
unpack_hash v = Vect.concat $ map unpack_word v

  -- Initialize array of round constants
kValues : (FromInteger n) => Unit -> Vect 64 n
kValues _ = Vect.fromList $ map fromInteger
  [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5
  , 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
  , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3
  , 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
  , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc
  , 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
  , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7
  , 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
  , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13
  , 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
  , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3
  , 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
  , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5
  , 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
  , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208
  , 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ]

hValues : (FromInteger n) => Unit -> Registers n
hValues _ =
  let
    -- Initialize hash values
    h0 : n
    h0 = fromInteger 0x6a09e667
    h1 : n
    h1 = fromInteger 0xbb67ae85
    h2 : n
    h2 = fromInteger 0x3c6ef372
    h3 : n
    h3 = fromInteger 0xa54ff53a
    h4 : n
    h4 = fromInteger 0x510e527f
    h5 : n
    h5 = fromInteger 0x9b05688c
    h6 : n
    h6 = fromInteger 0x1f83d9ab
    h7 : n
    h7 = fromInteger 0x5be0cd19
  in
  MkRegisters h0 h1 h2 h3 h4 h5 h6 h7

public export
sha256 : (FromInteger n, Show n, Eq n, Gt n, Add n, And n, Xor n, Invert n, FromNat n, Shl n, Shr n, Trunc n, Bitlist n, HasLength mt, ContainsBytes mt) => mt -> Vect 32 n
sha256 message =
  let
    k : Vect 64 n
    k = kValues ()

    padded_data : PaddedBits mt
    padded_data = MkPaddedBits message

    chunks : List (Vect 16 n)
    chunks = word_chunks padded_data

    -- Extend the first 16 words into the remaining 48 words w[16..63] of the message schedule array
    pass1_chunks : List (Vect 64 n)
    pass1_chunks = map extend_48_words chunks

    -- Initialize working variables to current hash value
    regs : Registers n
    regs = hValues ()

    init_idx_regs : IdxRegisters n
    init_idx_regs = MkIdxRegisters 0 regs

    out_regs : Registers n
    out_regs = reg $ foldl (\ir,chunk => transform_regs k ir chunk) init_idx_regs chunks

    -- Produce the final hash value (big-endian)
    result_hash : Vect 8 n
    result_hash =
      Vect.fromList
        [ a out_regs, b out_regs, c out_regs, d out_regs
        , e out_regs, f out_regs, g out_regs, h out_regs
        ]
  in
  unpack_hash result_hash
