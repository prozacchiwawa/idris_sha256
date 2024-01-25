module Numbers

import Data.Bin
import Decidable.Equality

public export
interface Add n where
  add : n -> n -> n

public export
implementation Add Nat where
  add a b = a + b

public export
interface Sub n where
  sub : n -> n -> n

public export
natSub : Nat -> Nat -> Nat
natSub x Z = x
natSub Z _ = Z
natSub (S x) (S y) = natSub x y

public export
implementation Sub Nat where
  sub = natSub

natOdd : Nat -> Bool
natOdd Z = False
natOdd (S x) = not (natOdd x)

public export
interface Odd n where
  odd : n -> Bool

public export
implementation Odd Nat where
  odd = natOdd

public export
interface Shl n where
  shl : Nat -> n -> n

public export
implementation Shl Nat where
  shl Z v = v
  shl (S n) v = shl n (2 * v)

public export
interface Shr n where
  shr : Nat -> n -> n

public export
natDivInner : Nat -> Nat -> Nat -> (Nat, Nat)
natDivInner ct n d =
  if d == 0 || n < d then
    (n, ct)
  else
    natDivInner (S ct) (sub n d) d

public export
natDiv : Nat -> Nat -> Nat
natDiv n d =
  let
    (_, ct) = natDivInner 0 n d
  in
  ct

public export
natMod : Nat -> Nat -> Nat
natMod n d =
  let
    (n, _) = natDivInner 0 n d
  in
  n

public export
implementation Shr Nat where
  shr a b = natDiv a 2

public export
interface Trunc n where
  trunc : Nat -> n -> n

public export
implementation Trunc Nat where
  trunc n v = natMod v (shl n 1)

public export
interface Bitlist n where
  bitlist : n -> List Nat

natBitList : Nat -> Nat -> List Nat
natBitList ct n =
  if shl ct 1 > n then
    []
  else
    ct :: (natBitList (ct + 1) n)

public export
implementation Bitlist Nat where
  bitlist = natBitList 0

public export
interface FromNat n where
  fromNat : Nat -> n

public export
implementation FromNat Nat where
  fromNat n = n

public export
interface FromInteger n where
  fromInteger : Integer -> n

public export
implementation FromInteger Integer where
  fromInteger i = cast i

public export
interface ToInteger n where
  toInteger : n -> Integer

public export
implementation ToInteger Integer where
  toInteger i = i

public export
implementation ToInteger Nat where
  toInteger i = cast i

binToInteger : Bin -> Integer
binToInteger BNil = 0
binToInteger (O Z v) = 1 + 2 * (binToInteger v)
binToInteger (O (S n) v) = 2 * (binToInteger (O n v))

public export
implementation ToInteger Bin where
  toInteger b = binToInteger b

public export
interface Gt n where
  gt : n -> n -> Bool

public export
implementation Gt Nat where
  gt a b = a > b

nat_xor_i : (Eq n, Add n, FromNat n, Trunc n, Shr n, Shl n) => List Nat -> n -> n -> n
nat_xor_i [] u v = fromNat 0
nat_xor_i (d :: tl) u v =
     let
       thisbit_u = trunc 1 (shr d u)
       thisbit_v = trunc 1 (shr d v)
       thisbit =
         if thisbit_u == thisbit_v then
           0
         else
           d
     in
     add (shl thisbit (fromNat 1)) (nat_xor_i tl u v)

nat_xor : (Eq n, Gt n, Add n, FromNat n, Trunc n, Shr n, Shl n, Bitlist n) => n -> n -> n
nat_xor u v =
  let
    plist = if gt u v then bitlist u else bitlist v
  in
  nat_xor_i plist u v

public export
interface Xor n where
  xor : n -> n -> n

public export
implementation Xor Nat where
  xor = nat_xor

nat_and_i : (Eq n, Add n, FromNat n, Trunc n, Shr n, Shl n) => List Nat -> n -> n -> n
nat_and_i [] _ _ = fromNat 0
nat_and_i (d :: tl) u v =
  let
    thisbit_u : n
    thisbit_u = trunc 1 (shr d u)

    thisbit_v : n
    thisbit_v = trunc 1 (shr d v)

    thisbit : Nat
    thisbit =
       if thisbit_u /= fromNat 0 && thisbit_v /= fromNat 0 then
         d
       else
         0
  in
  add (shl thisbit (fromNat 1)) (nat_and_i tl u v)

nat_and : (Eq n, Add n, Gt n, FromNat n, Trunc n, Shr n, Shl n, Bitlist n) => n -> n -> n
nat_and u v =
  let
    plist = if gt u v then bitlist u else bitlist v
  in
  nat_and_i plist u v

public export
interface And n where
  bitand : n -> n -> n

public export
implementation And Nat where
  bitand = nat_and

nat_not_i : (Eq n, Add n, Trunc n, Shr n, Shl n, FromNat n) => List Nat -> n -> n
nat_not_i [] u = fromNat 0
nat_not_i (d :: tl) u =
  let
    thisbit =
       if trunc 1 (shr d u) /= fromNat 0 then
         0
       else
         d
  in
  add (shl thisbit (fromNat 1)) (nat_not_i tl u)

public export
interface Invert n where
  invert : Nat -> n -> n

public export
implementation Invert Nat where
  invert count n =
    let
      fn1 : Nat
      fn1 = 1

      bl : List Nat
      bl = bitlist (sub (shl count fn1) fn1)
    in
    nat_not_i bl n

-- Bin
public export
implementation FromNat Bin where
  fromNat = nat2Bin

integer2Bin : Integer -> Bin
integer2Bin i with (decEq i 0)
  integer2Bin i | Yes iszero = BNil
  integer2Bin i | _ with (decEq (mod i 2) 1)
    integer2Bin i | _ | Yes one = O Z (integer2Bin (div i 2))
    integer2Bin i | _ | _ = oneMore (integer2Bin (div i 2))

public export
implementation FromInteger Bin where
  fromInteger i = integer2Bin i

public export
implementation Eq Bin where
  (==) BNil BNil = True
  (==) (O a c) (O b v) = a == b && c == v
  (==) _ _ = False

public export
implementation Gt Bin where
  gt BNil BNil = False
  gt (O a c) BNil = True
  gt BNil (O b v) = False
  gt (O Z c) (O Z v) = gt c v
  gt (O (S a) c) (O Z v) = True
  gt (O Z c) (O (S b) v) = False
  gt (O (S a) c) (O (S b) v) = gt (O a c) (O b v)

public export
implementation Add Bin where
  add a b = binAdd a b

public export
implementation And Bin where
  bitand a b = binAnd a b

public export
implementation Xor Bin where
  xor a b = binXor a b

public export
implementation Invert Bin where
  invert = binNot

public export
implementation Shl Bin where
  shl = binShl

public export
implementation Shr Bin where
  shr = binShr

public export
implementation Trunc Bin where
  trunc = binTrunc

bitlistBin : Nat -> Bin -> List Nat
bitlistBin _ BNil = []
bitlistBin n (O Z x) = n :: (bitlistBin (n+1) x)
bitlistBin n (O (S b) x) = n :: (bitlistBin (n+1) (O b x))

public export
implementation Bitlist Bin where
  bitlist = bitlistBin 0

public export
interface ToNat n where
  toNat : n -> Nat

public export
implementation ToNat Nat where
  toNat n = n

public export
implementation ToNat Integer where
  toNat i = cast i

public export
implementation ToNat Bin where
  toNat b = cast $ bin2Nat b
