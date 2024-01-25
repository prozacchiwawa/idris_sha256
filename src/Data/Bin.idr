module Data.Bin

import Decidable.Equality

%default total

decAsBool : Dec p -> Bool
decAsBool (Yes _) = True
decAsBool (No _)  = False

public export
less : Nat -> Nat -> Nat
less Z _ = Z
less a Z = a
less (S a) (S b) = less a b

public export
lessThan : Nat -> Nat -> Bool
lessThan Z (S a) = True
lessThan _ Z = False
lessThan (S a) (S b) = lessThan a b

sNotZ : {a : Nat} -> (S a = 0) -> Void
sNotZ Refl impossible

zNotS : {a : Nat} -> (0 = S a) -> Void
zNotS Refl impossible

-- Thanks: https://stackoverflow.com/questions/46507712/how-can-i-have-idris-automatically-prove-that-two-values-are-not-equal
fromFalse : (d : Dec p) -> {auto isFalse : decAsBool d = False} -> Not p
fromFalse (Yes _) {isFalse = Refl} impossible
fromFalse (No contra) = contra

data NotEq : a -> a -> Type where
    MkNotEq : {a : t} -> {b : t} -> Not (a = b) -> NotEq a b

public export data Bin = O Nat Bin | BNil

-- Thanks: https://www.reddit.com/r/Idris/comments/8yv5fn/using_deceq_in_proofs_extracting_and_applying_the/e2e8a6l/?context=3
O_injective : (O a v = O b w) -> (a = b, v = w)
O_injective Refl = (Refl, Refl)

O_bijective : (a = b) -> (v = w) -> (O a v = O b w)
O_bijective Refl Refl = Refl

total bnilNotO : (a : Nat) -> (b : Bin) -> (BNil = O a v) -> Void
bnilNotO a b p impossible

total notOBNil : (a : Nat) -> (b : Bin) -> (O a v = BNil) -> Void
notOBNil a b p impossible

total aNEBMeansNotEqual : (a : Nat) -> (b : Nat) -> (v : Bin) -> Dec (a = b) -> Dec (O a v = O b v)
aNEBMeansNotEqual a b v (Yes prf) = rewrite prf in Yes Refl
aNEBMeansNotEqual a b v (No contra) =
  No $ \prf =>
    let (ojAB, _) = O_injective prf in
    contra ojAB

total vNEWMeansNotEqual : (v : Bin) -> (w : Bin) -> Dec (v = w) -> Dec (O Z v = O Z w)
vNEWMeansNotEqual v w (Yes prf) = rewrite prf in Yes Refl
vNEWMeansNotEqual v w (No contra) = 
  No $ \prf =>
    let (_, ojVW) = O_injective prf in
    contra ojVW

avNEBWMeansNotEqual : (a : Nat) -> (v : Bin) -> (b : Nat) -> (w : Bin) -> Dec (a = b) -> Dec (v = w) -> Dec (O a v = O b w)
avNEBWMeansNotEqual a v b w (Yes prfAB) (Yes prfVW) = 
  rewrite prfAB in
  rewrite prfVW in
  Yes Refl
avNEBWMeansNotEqual a v b w (Yes prfAB) (No contraVW) = 
  No $ \prf => 
    let (_, ojVW) = O_injective prf in contraVW ojVW
avNEBWMeansNotEqual a v b w (No contraAB) _ = 
  No $ \prf =>
    let (ojAV, _) = O_injective prf in contraAB ojAV

eq0BNil : (O 0 BNil = O 0 BNil)
eq0BNil = Refl

doDecEqInner : (x1 : Bin) -> (x2 : Bin) -> Dec (x1 = x2)
doDecEqInner BNil                BNil              = Yes Refl
doDecEqInner BNil                (O b     w      ) = 
  No (bnilNotO {a=b} {b=w})
doDecEqInner (O a     v        ) BNil              = 
  No (notOBNil {a=a} {b=v})
doDecEqInner (O a     v        ) (O b     w      ) =
  avNEBWMeansNotEqual a v b w (decEq a b) (doDecEqInner v w)

DecEq Bin where
  decEq = doDecEqInner

public export
binIsZero : Bin -> Bool
binIsZero BNil = True
binIsZero (O _ _) = False

public export
oneMore : Bin -> Bin
oneMore BNil = BNil
oneMore (O a x) = O (S a) x

oneMoreZeroIsZero : oneMore BNil = BNil
oneMoreZeroIsZero = Refl

public export
flipFromLeft : Bin -> Bin
flipFromLeft BNil = O Z BNil
flipFromLeft (O (S a) x) = O Z (O a x)
flipFromLeft (O Z x) = assert_total (oneMore (flipFromLeft x))

public export
binInc : Bin -> Bin
binInc BNil = O Z BNil
binInc (O Z BNil) = O (S Z) BNil
binInc (O a v) = flipFromLeft (O a v)

public export
binDec : Bin -> Bin
binDec BNil = BNil
binDec (O Z BNil) = BNil
binDec (O Z (O a b)) = (O (S a) b)
{-
  0001 -- -> 1110
-}
binDec (O (S a) b) =
  assert_total (O Z (binDec (O a b)))

public export
nat2Bin : Nat -> Bin
nat2Bin Z = BNil
nat2Bin (S a) = binInc (nat2Bin a)

nat2BinZIsBNil : nat2Bin Z = BNil
nat2BinZIsBNil = Refl

public export
bin2Nat : Bin -> Nat
bin2Nat BNil = Z
bin2Nat (O Z v) =
  let m1 = assert_total (bin2Nat v) in
  let m2 = plus m1 m1 in
  S m2
bin2Nat (O (S a) v) =
  let m1 = assert_total (bin2Nat (O a v)) in
  plus m1 m1

bin2NatBNilIsZ : bin2Nat BNil = Z
bin2NatBNilIsZ = Refl

public export
binAddPlus : Bin -> Bin -> Bin
binAddPlus a b = nat2Bin (plus (bin2Nat a) (bin2Nat b))

public export
binAdd : Bin -> Bin -> Bin
binAdd BNil BNil = BNil
binAdd BNil v = v
binAdd c BNil = c
binAdd (O Z c) (O Z v) = oneMore (binInc (binAdd c v))
binAdd (O Z c) (O (S b) v) = O Z (assert_total (binAdd c (O b v)))
binAdd (O (S a) c) (O Z v) = O Z (assert_total (binAdd (O a c) v))
binAdd (O (S a) c) (O (S b) v) = oneMore (assert_total (binAdd (O a c) (O b v)))

azPlus : (a : Nat) -> (plus a Z = a)
azPlus Z = Refl
azPlus (S a1) = rewrite azPlus {a=a1} in Refl

zaPlus : (a : Nat) -> (plus Z a = a)
zaPlus Z = Refl
zaPlus (S a1) = Refl

testPlusA0 : (n : Nat) -> n = plus n 0
testPlusA0 Z = Refl
testPlusA0 (S k) =
  let rec = testPlusA0 {n=k} in
  rewrite rec in
  rewrite azPlus k in
  rewrite azPlus k in
  Refl

plusS1Eq2 : (n : Nat) -> plus n (S Z) = S n
plusS1Eq2 Z = Refl
plusS1Eq2 (S a) =
  let rec = plusS1Eq2 {n=a} in
  rewrite rec in Refl

add2NEqNP2 : (n : Nat) -> (a : Nat) -> S (plus n a) = plus n (S a)
add2NEqNP2 Z Z = Refl
add2NEqNP2 Z (S a) = Refl
add2NEqNP2 n Z =
  rewrite sym (testPlusA0 n) in
  rewrite (plusS1Eq2 n) in Refl

add2NEqNP2 (S n) (S a) =
  rewrite (add2NEqNP2 n (S a)) in
  Refl

moveSInPlus2 : (a : Nat) -> S (plus a a) = plus a (S a)
moveSInPlus2 Z = Refl
moveSInPlus2 a1 =
  rewrite sym (add2NEqNP2 a1 a1) in Refl

moveSInPlus3 : (a : Nat) -> S (plus a a) = plus (S a) a
moveSInPlus3 Z = Refl
moveSInPlus3 a1 = Refl

moveSInPlus4 : (a : Nat) -> plus (S a) a = S (plus a a)
moveSInPlus4 Z = Refl
moveSInPlus4 a1 = Refl

oneMoreIsTwiceAsMuch : (v : Bin) -> (plus (plus (bin2Nat v) (bin2Nat v)) (plus (bin2Nat v) (bin2Nat v))) = (bin2Nat (oneMore (oneMore v)))
oneMoreIsTwiceAsMuch BNil = Refl
oneMoreIsTwiceAsMuch (O Z v) = Refl
oneMoreIsTwiceAsMuch (O (S a) v) = Refl

oneMoreXIs2X : (b : Bin) -> bin2Nat (oneMore b) = plus (bin2Nat b) (bin2Nat b)
oneMoreXIs2X BNil = Refl
oneMoreXIs2X (O n a) = Refl

plusAZ : (a : Nat) -> (a = plus a Z)
plusAZ Z = Refl
plusAZ (S a) =
  rewrite plusAZ a in
  rewrite azPlus a in
  rewrite azPlus a in
  Refl

plusZA : (a : Nat) -> (a = plus Z a)
plusZA Z = Refl
plusZA (S a1) = Refl

plus00B0 : Z = plus Z Z
plus00B0 = Refl

saEqSb : (a : Nat) -> (b : Nat) -> Dec (S a = S b) -> Dec (a = b)
saEqSb Z Z (Yes prf) = Yes Refl
saEqSb a Z (Yes prf) =
  case decEq a Z of
    Yes prf1 =>
      rewrite prf1 in Yes Refl
    No contra => No contra
saEqSb a (S b) (Yes prf) =
  case decEq a (S b) of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra => No contra
saEqSb a b (No contra) =
  case decEq a b of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra => No contra

ssaNe1 : {a : Nat} -> (S (S a) = 1) -> Void
ssaNe1 Refl impossible

ssbNe1 : {b : Nat} -> (1 = S (S b)) -> Void
ssbNe1 Refl impossible

bEq0MeansSbEq1 : (b : Nat) -> Dec (0 = b) -> Dec (1 = S b)
bEq0MeansSbEq1 Z _ = Yes Refl
bEq0MeansSbEq1 (S b) _ = No $ \prfx => ssbNe1 prfx

saEqSb2 : (a : Nat) -> (b : Nat) -> (rw : Dec (a = b)) -> Dec (S a = S b)
saEqSb2 Z Z (Yes prf) = Yes Refl
saEqSb2 a Z (Yes prf) =
  case decEq a Z of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra => No $ \prfx => contra prf
saEqSb2 (S a) Z (No contra) =
  case decEq (S a) Z of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra1 => No ssaNe1
saEqSb2 a (S b) (Yes prf) =
  case decEq a (S b) of
    Yes prf1 => rewrite prf1 in Yes Refl
    No contra => No $ \prfx => contra prf
saEqSb2 Z (S b) (No contra) = No ssbNe1
saEqSb2 a b (No contra) =
  saEqSb (S a) (S b) (decEq (S (S a)) (S (S b)))

saEqSb3 : (a : Nat) -> (b : Nat) -> Dec (plus a 0 = plus b 0) -> Dec (a = b)
saEqSb3 a b prf =
  rewrite plusAZ a in
  rewrite plusAZ b in
  prf

oneIsNotTwo : (S Z) = (S (S Z)) -> Void
oneIsNotTwo p impossible

twoIsNotAPlus3 : {a : Nat} -> (S (S Z) = S (S (S a))) -> Void
twoIsNotAPlus3 Refl impossible

nextS : (a : Nat) -> (b : Nat) -> a = b -> S a = S b
nextS Z Z p = Refl
nextS Z (S y) p = absurd (zNotS p)
nextS (S x) Z p = absurd (sNotZ p)
nextS (S x) (S y) p =
  rewrite p in
  Refl

eqs : (a : Nat) -> (b : Nat) -> (S a = S b) -> (a = b)
eqs Z Z p = Refl
eqs Z (S b) p with (decEq b Z)
  eqs Z (S Z) p | Yes zp = absurd (oneIsNotTwo p)
  eqs Z (S b1) p | No c impossible
eqs (S a) Z p impossible
eqs (S a1) (S b1) p with (decEq a1 b1)
  eqs (S a1) (S b1) p | Yes p1 =
    rewrite p1 in
    Refl
  eqs (S Z) (S Z) p | No c1 = Refl
  eqs (S Z) (S (S b1)) p | No c1 impossible
  eqs (S (S a1)) (S Z) p | No c1 impossible
  eqs (S (S a1)) (S (S b1)) p | No c1 with (saEqSb a1 b1 (No c1))
    eqs (S (S a1)) (S (S b1)) p | No c1 | Yes ppp =
      let
        cproof : (S a1 = S b1)
        cproof = nextS a1 b1 ppp
      in
      absurd (c1 cproof)
    eqs (S (S a1)) (S (S b1)) p | No c1 | No qqq =
      let
        cproof = eqs (S (S a1)) (S (S b1)) p
        dproof = eqs (S a1) (S b1) cproof
        subp = eqs a1 b1 (assert_total dproof)
      in
      absurd (qqq subp)

plusA0EqPlusB0 : (a : Nat) -> (b : Nat) -> (rw : Dec (plus a 1 = plus b 1)) -> Dec (plus a 0 = plus b 0)
plusA0EqPlusB0 Z Z (Yes prf) = Yes Refl
plusA0EqPlusB0 a Z (Yes prf) =
  rewrite azPlus a in
  case decEq a Z of
    Yes prf1 => Yes prf1
    No contra => No contra
plusA0EqPlusB0 (S a1) (S b1) (Yes prf) =
  rewrite add2NEqNP2 a1 0 in
  rewrite add2NEqNP2 b1 0 in
  rewrite plusS1Eq2 a1 in
  rewrite plusS1Eq2 b1 in
  saEqSb2 a1 b1 (decEq a1 b1)
plusA0EqPlusB0 (S a1) (S b1) (No contra) =
  rewrite add2NEqNP2 a1 0 in
  rewrite add2NEqNP2 b1 0 in
  rewrite plusS1Eq2 a1 in
  rewrite plusS1Eq2 b1 in
  saEqSb2 a1 b1 (decEq a1 b1)
plusA0EqPlusB0 Z Z (No contra) = absurd (contra Refl)
plusA0EqPlusB0 Z (S b1) (Yes p) with (decEq Z (S b1))
  plusA0EqPlusB0 Z (S b1) (Yes p) | Yes p2 =
    rewrite sym (plusAZ b1) in
    Yes p2
  plusA0EqPlusB0 Z (S b1) (Yes p) | No c2 =
    rewrite sym (plusAZ b1) in
    No c2
plusA0EqPlusB0 Z (S b1) (No contra) with (decEq Z (S b1))
  plusA0EqPlusB0 Z (S b1) (No contra) | Yes p2 =
    rewrite sym (plusAZ b1) in
    Yes p2
  plusA0EqPlusB0 Z (S b1) (No contra) | No c2 =
    rewrite sym (plusAZ b1) in
    No c2
plusA0EqPlusB0 (S a1) Z (No contra) =
  let
    res = saEqSb (plus a1 1) Z (No contra)
  in
  rewrite add2NEqNP2 a1 Z in
  res

plusA1EqPlusB1 : (a : Nat) -> (b : Nat) -> Dec (a = b) -> Dec (plus a 1 = plus b 1)
plusA1EqPlusB1 a b (Yes prf) =
  rewrite prf in Yes Refl
plusA1EqPlusB1 a b (No contra) =
  let re = plusA0EqPlusB0 a b (decEq (plus a 1) (plus b 1)) in
  rewrite plusS1Eq2 a in
  rewrite plusS1Eq2 b in
  saEqSb2 a b (No contra)

removeOneS : (a : Nat) -> (b : Nat) -> Dec (a = b) -> Dec (S a = S b)
removeOneS a b (Yes prf) =
  rewrite prf in Yes Refl
removeOneS a b (No contra) =
  rewrite plusAZ a in
  rewrite plusAZ b in
  saEqSb2 (plus a 0) (plus b 0) (decEq (plus a 0) (plus b 0))

twoTimesAIsZeroIfAIs2 : (a : Nat) -> Dec (plus a a = 0) -> Dec (a = 0)
twoTimesAIsZeroIfAIs2 a prf =
  saEqSb3 a 0 (decEq (plus a 0) 0)

twoTimesAIsZeroIfAIs : (a : Nat) -> Dec (a = 0) -> Dec (plus a a = 0)
twoTimesAIsZeroIfAIs a (Yes prf) = rewrite prf in Yes Refl
twoTimesAIsZeroIfAIs Z _ = Yes Refl
twoTimesAIsZeroIfAIs (S a) (No contra) =
  rewrite sym (add2NEqNP2 a a) in
  No $ \prf =>
    sNotZ {a=S (plus a a)} prf

fourIsNotZero : (S (S (S (S Z))) = 0) -> Void
fourIsNotZero Refl impossible

fourIsNotTwo : (S (S (S (S Z))) = S (S Z)) -> Void
fourIsNotTwo Refl impossible

sixIsNotZero : (S (S (S (S (S (S Z))))) = plus 0 0) -> Void
sixIsNotZero Refl impossible

sixIsNotTwo : (S (S (S (S (S (S Z))))) = plus 1 1) -> Void
sixIsNotTwo Refl impossible

sixIsNotFour : (S (S (S (S (S (S Z))))) = plus 2 2) -> Void
sixIsNotFour Refl impossible

fourIsNotAPlus6 : {a : Nat} -> (S (S (S (S Z))) = S (S (S (S (S (S (plus a a))))))) -> Void
fourIsNotAPlus6 Refl impossible

eightIsNotZero : (S (S (S (S (S (S (S (S Z))))))) = 0) -> Void
eightIsNotZero Refl impossible

eightIsNotTwo : (S (S (S (S (S (S (S (S Z))))))) = (S (S Z))) -> Void
eightIsNotTwo Refl impossible

eightIsNotFour : (S (S (S (S (S (S (S (S Z))))))) = (S (S (S (S Z))))) -> Void
eightIsNotFour Refl impossible

eightIsNotSix : (S (S (S (S (S (S (S (S Z))))))) = (S (S (S (S (S (S Z))))))) -> Void
eightIsNotSix Refl impossible

sixIsNotAPlus8 : {a : Nat} -> (S (S (S (S (S (S Z))))) = S (S (S (S (S (S (S (S (plus a a))))))))) -> Void
sixIsNotAPlus8 Refl impossible

eightIsNotAPlus10 : {a : Nat} -> (S (S (S (S (S (S (S (S Z))))))) = S (S (S (S (S (S (S (S (S (S (plus a a))))))))))) -> Void
eightIsNotAPlus10 Refl impossible

tenIsNotZero : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus 0 0) -> Void
tenIsNotZero Refl impossible

tenIsNotTwo : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus (S Z) (S Z)) -> Void
tenIsNotTwo Refl impossible

tenIsNotFour : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus (S (S Z)) (S (S Z))) -> Void
tenIsNotFour Refl impossible

tenIsNotSix : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus (S (S (S Z))) (S (S (S Z)))) -> Void
tenIsNotSix Refl impossible

tenIsNotEight : (S (S (S (S (S (S (S (S (S (S Z))))))))) = plus (S (S (S (S Z)))) (S (S (S (S Z))))) -> Void
tenIsNotEight Refl impossible

tenIsNotAPlus12 : {a : Nat} -> (S (S (S (S (S (S (S (S (S (S Z))))))))) = S (S (S (S (S (S (S (S (S (S (S (S (plus a a))))))))))))) -> Void
tenIsNotAPlus12 Refl impossible

fourPlusAIsNot0 : {a : Nat} -> (S (S (S (S a))) = 0) -> Void
fourPlusAIsNot0 Refl impossible

fourPlusAIsNot2 : {a : Nat} -> (S (S (S (S a))) = 2) -> Void
fourPlusAIsNot2 Refl impossible

a2Pa4 : (a : Nat) -> Dec (2 = a) -> Dec (4 = plus a a)
a2Pa4 (S (S Z)) _ = Yes Refl
a2Pa4 a (Yes r) =
  rewrite r in
  rewrite sym r in Yes Refl
a2Pa4 Z (No contra) = No fourIsNotZero
a2Pa4 (S Z) _ = No fourIsNotTwo
a2Pa4 (S (S (S a))) (No contra) =
  rewrite sym (add2NEqNP2 a (S (S a))) in
  rewrite sym (add2NEqNP2 a (S a)) in
  rewrite sym (add2NEqNP2 a a) in
  No fourIsNotAPlus6

plusZZPlus4N : {n : Nat} -> (S (S (S (S (plus n n)))) = plus 0 0) -> Void
plusZZPlus4N Refl impossible

plus2NEq0 : {n : Nat} -> (S (S n) = 0) -> Void
plus2NEq0 Refl impossible

plus2NEq1 : {n : Nat} -> (S (S n) = 1) -> Void
plus2NEq1 Refl impossible

plus4NNEqPlus2APlus2A : (n : Nat) -> (S (S (S (S (plus n n)))) = plus (S (S n)) (S (S n)))
plus4NNEqPlus2APlus2A n =
  rewrite sym (add2NEqNP2 n (S n)) in
  rewrite sym (add2NEqNP2 n n) in
  Refl

a4Pa2 : (n : Nat) -> (a : Nat) -> Dec (S (S (S (S (plus n n)))) = plus a a) -> Dec (S (S n) = a)
a4Pa2 n Z prf = No plus2NEq0
a4Pa2 n (S Z) prf = No plus2NEq1
a4Pa2 Z (S (S Z)) p = Yes Refl
a4Pa2 Z (S (S (S a))) p = No twoIsNotAPlus3
a4Pa2 n (S (S a)) p = decEq (S (S n)) (S (S a))

a3Pa6 : (a : Nat) -> Dec (3 = a) -> Dec (6 = plus a a)
a3Pa6 (S (S (S Z))) _ = Yes Refl
a3Pa6 a (Yes r) =
  rewrite r in
  rewrite sym r in Yes Refl
a3Pa6 Z (No contra) = No sixIsNotZero
a3Pa6 (S Z) _ = No sixIsNotTwo
a3Pa6 (S (S Z)) _ = No sixIsNotFour
a3Pa6 (S (S (S (S a)))) (No contra) =
  rewrite sym (add2NEqNP2 a (S (S (S a)))) in
  rewrite sym (add2NEqNP2 a (S (S a))) in
  rewrite sym (add2NEqNP2 a (S a)) in
  rewrite sym (add2NEqNP2 a a) in
  No sixIsNotAPlus8

a4Pa8 : (a : Nat) -> Dec (4 = a) -> Dec (8 = plus a a)
a4Pa8 (S (S (S (S Z)))) _ = Yes Refl
a4Pa8 a (Yes r) =
  rewrite r in
  rewrite sym r in Yes Refl
a4Pa8 Z (No contra) = No eightIsNotZero
a4Pa8 (S Z) _ = No eightIsNotTwo
a4Pa8 (S (S Z)) _ = No eightIsNotFour
a4Pa8 (S (S (S Z))) _ = No eightIsNotSix
a4Pa8 (S (S (S (S (S a))))) (No contra) =
  rewrite sym (add2NEqNP2 a (S (S (S (S a))))) in
  rewrite sym (add2NEqNP2 a (S (S (S a)))) in
  rewrite sym (add2NEqNP2 a (S (S a))) in
  rewrite sym (add2NEqNP2 a (S a)) in
  rewrite sym (add2NEqNP2 a a) in
  No eightIsNotAPlus10

fourPlusNNEqPlusN2N2 : (n : Nat) -> (S (S (S (S (plus n n)))) = plus (S (S n)) (S (S n)))
fourPlusNNEqPlusN2N2 n =
  rewrite sym (add2NEqNP2 n (S n)) in
  rewrite sym (add2NEqNP2 n n) in
  Refl

threePlusAIsNot2 : {a : Nat} -> (S (S (S a)) = S (S Z)) -> Void
threePlusAIsNot2 Refl impossible

twoIsNotThreePlusA : {a : Nat} -> (S (S Z) = S (S (S a))) -> Void
twoIsNotThreePlusA Refl impossible

fivePlusAIsNotFour : {a : Nat} -> (S (S (S (S (S a)))) = S (S (S (S Z)))) -> Void
fivePlusAIsNotFour Refl impossible

ssNEqPlusAA : (n : Nat) -> (a : Nat) -> Dec (S (S n) = a) -> Dec (S (S (S (S (plus n n)))) = plus a a)
ssNEqPlusAA Z a p = a2Pa4 a p
ssNEqPlusAA (S Z) a p = a3Pa6 a p
ssNEqPlusAA (S (S Z)) a p = a4Pa8 a p
ssNEqPlusAA n a (Yes p) =
  rewrite sym p in
  rewrite fourPlusNNEqPlusN2N2 n in
  let ssres1 = saEqSb (S (S (S (S (plus n n))))) (S (S n)) in
  let ssres2 = saEqSb (S (S (S (plus n n)))) (S n) in
  Yes Refl
ssNEqPlusAA n Z (No contra) = No fourPlusAIsNot0
ssNEqPlusAA n (S Z) (No contra) = No fourPlusAIsNot2
ssNEqPlusAA (S n) (S (S Z)) (No contra) = No fivePlusAIsNotFour
ssNEqPlusAA n (S (S a)) (No contra) =
  rewrite fourPlusNNEqPlusN2N2 n in
  decEq (S (S (plus n (S (S n))))) (S (S (plus a (S (S a)))))

canHalveAdds4 : (n : Nat) -> (a : Nat) -> (S (S n) = plus a a) -> ((S (S (S (S (plus n n))))) = plus (plus a a) (plus a a))
canHalveAdds4 n a prf =
  rewrite sym prf in
  rewrite sym (moveSInPlus2 (S n)) in
  rewrite sym (moveSInPlus2 n) in Refl

fourSBackIn : (a : Nat) -> (S (S (S (S (plus (plus a a) (plus a a))))) = plus (plus (S a) (S a)) (plus (S a) (S a)))
fourSBackIn Z = Refl
fourSBackIn (S a) =
  rewrite sym (add2NEqNP2 a a) in
  rewrite sym (add2NEqNP2 a (S a)) in
  rewrite sym (add2NEqNP2 a a) in
  rewrite sym (add2NEqNP2 (plus a a) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (plus a a) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus a a) (S (S (S (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus a a) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus a a) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (plus a a) (plus a a)) in
  Refl

ssPlusAAEqPlusSaSa : (a : Nat) -> (S (S (plus a a)) = plus (S a) (S a))
ssPlusAAEqPlusSaSa Z = Refl
ssPlusAAEqPlusSaSa (S a) =
  rewrite moveSInPlus2 (S a) in
  Refl

oneMoreFlipFromNatEqSb2NOAV : (a : Nat) -> (v : Bin) -> (S (S (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) = bin2Nat (oneMore (flipFromLeft (O a v))))
oneMoreFlipFromNatEqSb2NOAV Z BNil = Refl
oneMoreFlipFromNatEqSb2NOAV (S a) v =
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in
  Refl
oneMoreFlipFromNatEqSb2NOAV Z (O a1 v1) =
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1))) (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1)))) in
  rewrite oneMoreXIs2X (oneMore (flipFromLeft (O a1 v1))) in
  rewrite sym (oneMoreFlipFromNatEqSb2NOAV a1 v1) in
  rewrite sym (add2NEqNP2 (S (S (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1))))) (S (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1))))) in
  rewrite sym (add2NEqNP2 (S (S (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1))))) (plus (bin2Nat (O a1 v1)) (bin2Nat (O a1 v1)))) in
  Refl

ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV : (v : Bin) -> (S (S (bin2Nat (oneMore v))) = (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v))))
ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV BNil = Refl
ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV (O Z BNil) = Refl
ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV (O (S a) v) =
  rewrite moveSInPlus2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) in
  Refl
ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV (O Z (O a v)) =
  rewrite sym (oneMoreFlipFromNatEqSb2NOAV a v) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (S (plus (bin2Nat (O a v)) (bin2Nat (O a v))))) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in
  Refl

canHalveAdds4Start : (v : Bin) -> S (S (S (S (plus (bin2Nat (oneMore v)) (bin2Nat (oneMore v)))))) = plus (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v))) (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v)))
canHalveAdds4Start v =
  canHalveAdds4 (bin2Nat (oneMore v)) (bin2Nat (flipFromLeft v)) (ssBin2NatOneMoreVEqPlus2XBin2NatFLipFromLeftV v)

canHalveAdds8Start : (v : Bin) -> S (S (plus (bin2Nat v) (bin2Nat v))) = bin2Nat (oneMore (flipFromLeft v))
canHalveAdds8Start BNil = Refl
canHalveAdds8Start (O a v) =
  rewrite oneMoreFlipFromNatEqSb2NOAV a v in
  Refl

moveAllS1 : (x : Nat) -> S (S (S (S (plus (plus (plus x x) (plus x x)) (plus (plus x x) (plus x x)))))) = S (plus (plus (plus x x) (S (plus x x))) (S (plus (plus x x) (S (plus x x)))))
moveAllS1 Z = Refl
moveAllS1 (S a) =
  rewrite sym (add2NEqNP2 a a) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus a a) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus a a) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (plus a a) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (plus (plus a a) (plus a a)))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (plus (plus a a) (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (plus (plus a a) (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (plus (plus a a) (plus a a))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (S (S (plus (plus a a) (plus a a)))))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (S (plus (plus a a) (plus a a))))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (plus (plus a a) (plus a a)))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (plus (plus a a) (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (plus (plus a a) (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (plus (plus a a) (plus a a))) in
  Refl

moveAllS2 : (x : Nat) -> S (S (S (S (S (plus (plus (plus x x) (S (plus x x))) (S (plus (plus x x) (S (plus x x))))))))) = S (S (S (S (S (S (S (S (plus (plus (plus x x) (plus x x)) (plus (plus x x) (plus x x))))))))))
moveAllS2 Z = Refl
moveAllS2 (S a) =
  rewrite sym (add2NEqNP2 a a) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (S (plus a a)) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus a a) (S (S (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus a a) (S (plus a a))) in
  rewrite sym (add2NEqNP2 (plus a a) (plus a a)) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (plus (plus a a) (plus a a)))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (plus (plus a a) (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (plus (plus a a) (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (plus (plus a a) (plus a a))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (S (S (plus (plus a a) (plus a a)))))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (S (plus (plus a a) (plus a a))))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (S (plus (plus a a) (plus a a)))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (S (plus (plus a a) (plus a a))))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (S (plus (plus a a) (plus a a)))) in
  rewrite sym (add2NEqNP2 (plus (plus a a) (plus a a)) (plus (plus a a) (plus a a))) in
  Refl

prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV : (v : Bin) -> S (S (S (S (plus (bin2Nat (oneMore v)) (bin2Nat (oneMore v)))))) = plus (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v))) (plus (bin2Nat (flipFromLeft v)) (bin2Nat (flipFromLeft v)))
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV BNil = Refl
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV (O Z BNil) = Refl
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV (O (S a) BNil) =
  rewrite moveAllS1 (bin2Nat (O a BNil)) in Refl
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV (O (S a) (O b w)) =
  rewrite moveAllS1 (bin2Nat (O a (O b w))) in Refl
prove2XBin2NatFlipFromLeftVEqBin2NatOneMoreV (O Z (O a v)) =
  rewrite moveAllS2 (bin2Nat (O a v)) in
  rewrite sym (oneMoreFlipFromNatEqSb2NOAV a v) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (S (plus (bin2Nat (O a v)) (bin2Nat (O a v))))) in
  rewrite sym (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in
  rewrite sym (add2NEqNP2 (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) (S (S (S (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))))))) in
  rewrite sym (add2NEqNP2 (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) (S (S (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v))))))) in
  rewrite sym (add2NEqNP2 (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) (S (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))))) in
  rewrite sym (add2NEqNP2 (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) (plus (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v))))) in
  Refl

public export
testBin2Nat : (b : Bin) -> S (bin2Nat b) = bin2Nat (binInc b)
testBin2Nat BNil = Refl
testBin2Nat (O Z BNil) = Refl
testBin2Nat (O Z (O Z v)) =
  rewrite sym (add2NEqNP2 (plus (bin2Nat v) (bin2Nat v)) (plus (bin2Nat v) (bin2Nat v))) in
  rewrite oneMoreIsTwiceAsMuch v in
  rewrite oneMoreXIs2X (oneMore (flipFromLeft v)) in
  rewrite oneMoreXIs2X (oneMore v) in
  rewrite oneMoreXIs2X (flipFromLeft v) in
  rewrite canHalveAdds4Start v in Refl
testBin2Nat (O Z (O (S a) v)) =
  rewrite (add2NEqNP2 (plus (bin2Nat (O a v)) (bin2Nat (O a v))) (plus (bin2Nat (O a v)) (bin2Nat (O a v)))) in Refl
testBin2Nat (O (S a) BNil) = Refl
testBin2Nat (O (S a) (O b v)) = Refl

public export
sAISBin2NatBinIncNat2BinA : (a : Nat) -> S a = bin2Nat (binInc (nat2Bin a))
sAISBin2NatBinIncNat2BinA Z = Refl
sAISBin2NatBinIncNat2BinA (S a) =
  rewrite sym (testBin2Nat (binInc (nat2Bin a))) in
  rewrite sAISBin2NatBinIncNat2BinA a in
  Refl

public export
bin2NatIsReflexiveWithNat2Bin : (a : Nat) -> a = (bin2Nat (nat2Bin a))
bin2NatIsReflexiveWithNat2Bin Z = Refl
bin2NatIsReflexiveWithNat2Bin (S a) =
  rewrite sAISBin2NatBinIncNat2BinA a in
  Refl

showBinInternal : Bin -> String
showBinInternal BNil = ""
showBinInternal (O Z v) = (assert_total (showBinInternal v)) ++ "1"
showBinInternal (O (S a) v) = (assert_total (showBinInternal (O a v))) ++ "0"

public export
showBin : Bin -> String
showBin BNil = "0"
showBin x = showBinInternal x

public export
implementation Show Bin where
  show = showBin

public export
Cast Bin Nat where
  cast = bin2Nat

public export
Cast Nat Bin where
  cast = nat2Bin

public export
binEq : Bin -> Bin -> Bool
binEq BNil BNil = True
binEq BNil (O b y) = False
binEq (O a x) BNil = False
binEq (O Z x) (O Z y) = assert_total (binEq x y)
binEq (O Z x) (O (S b) y) = False
binEq (O (S a) x) (O Z y) = False
binEq (O (S a) x) (O (S b) y) = assert_total (binEq (O a x) (O b y))

public export
natEq : Nat -> Nat -> Bool
natEq Z Z = True
natEq (S n) Z = False
natEq Z (S n) = False
natEq (S n) (S m) = natEq n m

public export
binEqAA : (a : Bin) -> binEq a a = True
binEqAA BNil =
  Refl
binEqAA (O Z v) =
  rewrite assert_total (binEqAA v) in
  Refl
binEqAA (O (S a) BNil) =
  rewrite assert_total (binEqAA (O a BNil)) in
  Refl
binEqAA (O (S a) v) =
  rewrite assert_total (binEqAA (O a v)) in
  Refl

Eq Bin where
  (==) = binEq

public export
chop : Nat -> Bin -> Bin
chop _ BNil = BNil
chop Z (O _ _) = BNil
chop (S n) (O Z v) = O Z (chop n v)
chop (S n) (O (S m) v) = chop n (O m v)

public export
natOdd : Nat -> Nat
natOdd Z = Z
natOdd (S Z) = S Z
natOdd (S (S n)) = natOdd n

public export
plusSNPlusSnIsSSn : (n : Nat) -> (S (n + (S n))) = S (S (n + n))
plusSNPlusSnIsSSn Z = Refl
plusSNPlusSnIsSSn (S m) =
  rewrite add2NEqNP2 m (S m) in
  Refl

public export
plusAAIsEven : (a : Nat) -> natOdd (a + a) = Z
plusAAIsEven Z = Refl
plusAAIsEven (S n) =
  rewrite plusSNPlusSnIsSSn n in
  rewrite plusAAIsEven n in
  Refl

public export
aPlus2SameEvenness : (a : Nat) -> natOdd a = natOdd (S (S a))
aPlus2SameEvenness Z = Refl
aPlus2SameEvenness (S n) = Refl

public export
contradictionOdd : natOdd 0 = 1 -> Void
contradictionOdd prf impossible

public export
onePlusOddIsEven : (q : Nat) -> natOdd q = S Z -> natOdd (S q) = Z
onePlusOddIsEven Z prf = absurd (contradictionOdd prf)
onePlusOddIsEven (S Z) prf = Refl
onePlusOddIsEven (S (S o)) prf1 =
  rewrite sym (onePlusOddIsEven o prf1) in
  Refl

public export
contradictionEven : natOdd 1 = 0 -> Void
contradictionEven prf impossible

public export
onePlusEvenIsOdd : (a : Nat) -> natOdd a = Z -> natOdd (S a) = S Z
onePlusEvenIsOdd Z prf = Refl
onePlusEvenIsOdd (S Z) prf = absurd (contradictionEven prf)
onePlusEvenIsOdd (S (S o)) prf1 =
  rewrite sym (onePlusEvenIsOdd o prf1) in
  Refl

public export
chop0AnyIs0 : (v : Bin) -> bin2Nat (chop 0 v) = 0
chop0AnyIs0 BNil = Refl
chop0AnyIs0 (O x b) = Refl

public export
chop1IsOddIfBIsOdd : (b : Bin) -> bin2Nat (chop 1 b) = natOdd (bin2Nat b)
chop1IsOddIfBIsOdd BNil = Refl
chop1IsOddIfBIsOdd (O Z BNil) = Refl
chop1IsOddIfBIsOdd (O Z v) =
  let
    b2nvIsEven : (natOdd ((bin2Nat v) + (bin2Nat v)) = Z)
    b2nvIsEven =
      rewrite plusAAIsEven (bin2Nat v) in
      Refl

    exprOdd : natOdd (S ((bin2Nat v) + (bin2Nat v))) = S Z
    exprOdd =
      rewrite onePlusEvenIsOdd ((bin2Nat v) + (bin2Nat v)) b2nvIsEven in
      Refl
  in
  rewrite exprOdd in
  rewrite chop0AnyIs0 v in
  Refl
chop1IsOddIfBIsOdd (O (S x) v) =
  rewrite plusAAIsEven (bin2Nat (O x v)) in
  Refl

div2Nat : Nat -> Nat
div2Nat Z = Z
div2Nat (S Z) = Z
div2Nat (S (S n)) = S (div2Nat n)

pow2Nat : Nat -> Nat
pow2Nat Z = S Z
pow2Nat (S n) = (pow2Nat n) + (pow2Nat n)

binShr1 : Bin -> Bin
binShr1 BNil = BNil
binShr1 (O Z x) = x
binShr1 (O (S a) x) = O a x

binOdd : Bin -> Nat
binOdd BNil = Z
binOdd (O Z _) = S Z
binOdd (O (S a) x) = Z

binOddEqNatOdd : (b : Bin) -> natOdd (bin2Nat b) = binOdd b
binOddEqNatOdd BNil = Refl
binOddEqNatOdd (O Z x) =
  let
    twiceBin2NatXIsEven : (natOdd ((bin2Nat x) + (bin2Nat x)) = 0)
    twiceBin2NatXIsEven =
      rewrite plusAAIsEven (bin2Nat x) in
      Refl

    exprOdd : natOdd (S (plus (bin2Nat x) (bin2Nat x))) = S Z
    exprOdd =
      rewrite onePlusEvenIsOdd ((bin2Nat x) + (bin2Nat x)) twiceBin2NatXIsEven in
      Refl
  in
  exprOdd
binOddEqNatOdd (O (S a) x) =
  rewrite plusAAIsEven (bin2Nat (O a x)) in
  Refl

div2NatOnePlusAPAIsA : (a : Nat) -> div2Nat (S (a + a)) = a
div2NatOnePlusAPAIsA Z = Refl
div2NatOnePlusAPAIsA (S x) =
  rewrite sym (add2NEqNP2 x x) in
  rewrite div2NatOnePlusAPAIsA x in
  Refl

div2NatPlusAAIsA : (a : Nat) -> div2Nat (a + a) = a
div2NatPlusAAIsA Z = Refl
div2NatPlusAAIsA (S x) =
  rewrite sym (add2NEqNP2 x x) in
  rewrite div2NatPlusAAIsA x in
  Refl

public export
plusOaxOaxIsOSax : (a : Nat) -> (x : Bin) -> bin2Nat (O (S a) x) = plus (bin2Nat (O a x)) (bin2Nat (O a x))
plusOaxOaxIsOSax Z BNil = Refl
plusOaxOaxIsOSax Z (O b v) = Refl
plusOaxOaxIsOSax (S m) BNil = Refl
plusOaxOaxIsOSax (S m) (O b v) = Refl

oNotBNil : {b : Nat} -> {z : Bin} -> (O b z) = BNil -> Void
oNotBNil {b = Z} {z = BNil} Refl impossible
oNotBNil {b = (S v)} {z = BNil} Refl impossible
oNotBNil {b = Z} {z = (O s t)} Refl impossible
oNotBNil {b = (S v)} {z = (O s t)} Refl impossible

bNilNotO : {b : Nat} -> {z : Bin} -> BNil = (O b z) -> Void
bNilNotO {b = Z} {z = BNil} Refl impossible
bNilNotO {b = (S v)} {z = BNil} Refl impossible
bNilNotO {b = Z} {z = (O s t)} Refl impossible
bNilNotO {b = (S v)} {z = (O s t)} Refl impossible

plusXXEqZ : (x : Nat) -> plus x x = 0 -> x = 0
plusXXEqZ Z p = Refl
plusXXEqZ (S a) p = absurd (sNotZ p)

zEqPlusXX : (x : Nat) -> 0 = plus x x -> x = 0
zEqPlusXX Z p = Refl
zEqPlusXX (S a) p = absurd (zNotS p)

bin2NatOIsNotBNil : (b : Nat) -> (z : Bin) -> bin2Nat (O b z) = 0 -> Void
bin2NatOIsNotBNil Z BNil Refl impossible
bin2NatOIsNotBNil (S v) BNil p =
  let
    pzero : (bin2Nat (O v BNil) = 0)
    pzero = plusXXEqZ (bin2Nat (O v BNil)) p
  in
  absurd (bin2NatOIsNotBNil v BNil pzero)
bin2NatOIsNotBNil Z (O s t) p = absurd (sNotZ p)
bin2NatOIsNotBNil (S v) (O s t) p =
  let
    pzero : (bin2Nat (O v (O s t)) = 0)
    pzero = plusXXEqZ (bin2Nat (O v (O s t))) p
  in
  absurd (bin2NatOIsNotBNil v (O s t) pzero)

swapEqNat : (a : Nat) -> (b : Nat) -> a = b -> b = a
swapEqNat Z Z p = Refl
swapEqNat (S a) Z p = absurd (sNotZ p)
swapEqNat Z (S b) p = absurd (zNotS p)
swapEqNat (S a) (S b) p =
  rewrite p in
  Refl

swapEqBin : (a : Bin) -> (b : Bin) -> a = b -> b = a
swapEqBin BNil BNil p = Refl
swapEqBin (O s t) BNil p = absurd (oNotBNil p)
swapEqBin BNil (O x y) p = absurd (bNilNotO p)
swapEqBin (O s t) (O x y) p =
  rewrite p in
  Refl

bin2NatOIsNotBNil2 : (b : Nat) -> (z : Bin) -> 0 = bin2Nat (O b z) -> Void
bin2NatOIsNotBNil2 Z BNil Refl impossible
bin2NatOIsNotBNil2 (S v) x p =
  let
    ip : (plus (bin2Nat (O v x)) (bin2Nat (O v x)) = 0)
    ip = swapEqNat 0 (plus (bin2Nat (O v x)) (bin2Nat (O v x))) p

    pzero : (bin2Nat (O v x) = 0)
    pzero = plusXXEqZ (bin2Nat (O v x)) ip
  in
  absurd (bin2NatOIsNotBNil v x pzero)

plusAAEqPlusBBMeansAEqB : (a : Nat) -> (b : Nat) -> (plus a a = plus b b) -> (a = b)
plusAAEqPlusBBMeansAEqB Z Z p = Refl
plusAAEqPlusBBMeansAEqB (S a) Z p impossible
plusAAEqPlusBBMeansAEqB Z (S b) p impossible
plusAAEqPlusBBMeansAEqB (S a) (S b) p =
  let
    p1 : (S (S (plus a a)) = S (S (plus b b)))
    p1 =
      rewrite add2NEqNP2 a a in
      rewrite add2NEqNP2 b b in
      p

    p2 : (S (plus a a) = S (plus b b))
    p2 = eqs (S (plus a a)) (S (plus b b)) p1

    p3 : (plus a a = plus b b)
    p3 = eqs (plus a a) (plus b b) p2
  in
  rewrite plusAAEqPlusBBMeansAEqB a b p3 in
  Refl

public export
oddNotEqualEven : (a : Nat) -> (b : Nat) -> (S (plus a a) = plus b b) -> Void
oddNotEqualEven Z Z p impossible
oddNotEqualEven Z (S b) p =
  let
    p1 : (1 = S (S (plus b b)))
    p1 =
      rewrite add2NEqNP2 b b in
      p

    p2 : (Z = S (plus b b))
    p2 =
      eqs Z (S (plus b b)) p1
  in
  zNotS p2
oddNotEqualEven (S a) Z p = sNotZ p
oddNotEqualEven (S a) (S b) p =
  let
    p1 : (S (plus a (S a)) = plus b (S b))
    p1 = eqs (S (plus a (S a))) (plus b (S b)) p

    p2 : (S (S (plus a a)) = S (plus b b))
    p2 =
      rewrite add2NEqNP2 a a in
      rewrite add2NEqNP2 b b in
      p1

    p3 : (S (plus a a) = plus b b)
    p3 = eqs (S (plus a a)) (plus b b) p2
  in
  oddNotEqualEven a b p3

public export
binIncOneMoreIsO0 : (b : Bin) -> binInc (oneMore b) = O 0 b
binIncOneMoreIsO0 BNil = Refl
binIncOneMoreIsO0 (O x y) = Refl

public export
anyYO0NotBNil : (y : Bin) -> O 0 y = BNil -> Void
anyYO0NotBNil BNil Refl impossible
anyYO0NotBNil (O f g) Refl impossible

public export
oneMoreNETwoMore : (s : Nat) -> (t : Bin) -> oneMore (O s t) = oneMore (oneMore (O s t)) -> Void
oneMoreNETwoMore Z BNil Refl impossible
oneMoreNETwoMore Z (O s t) Refl impossible
oneMoreNETwoMore (S x) BNil Refl impossible
oneMoreNETwoMore (S x) (O s t) Refl impossible

public export
collapseEqTail : (c : Nat) -> (d : Nat) -> (b : Bin) -> (q : Bin) -> (O c b = O d q) -> (b = q)
collapseEqTail c d b q p =
  let
    (_, tailProof) = O_injective p
  in
  tailProof

public export
reverseProof : (a = b) -> (b = a)
reverseProof Refl = Refl

public export
o0BNilN1 : O 0 BNil = O 1 BNil -> Void
o0BNilN1 Refl impossible

public export
oneLessShift : (f : Nat) -> (e : Bin) -> (g : Bin) -> (O (S f) e) = (O (S f) g) -> (O f e = O f g)
oneLessShift Z BNil BNil p = Refl
oneLessShift Z BNil (O x y) Refl impossible
oneLessShift Z (O s t) BNil Refl impossible
oneLessShift Z (O s t) (O x y) p =
  let
    proofTEqY : (O s t = O x y)
    proofTEqY = collapseEqTail 1 1 (O s t) (O x y) p
  in
  rewrite proofTEqY in
  Refl
oneLessShift (S a) BNil BNil p = Refl
oneLessShift (S a) BNil (O x y) Refl impossible
oneLessShift (S a) (O s t) BNil Refl impossible
oneLessShift (S a) (O s t) (O x y) p =
  let
    p2 : (O (S a) (O s t) = O (S a) (O x y))
    p2 =
      let
        (shiftEq, tailEq) = O_injective p
        reducedShiftEq = eqs (S a) (S a) shiftEq
      in
      O_bijective reducedShiftEq tailEq
  in
  p2

public export
shiftIsEqual : (c : Nat) -> (d : Nat) -> (b : Bin) -> (q : Bin) -> O c b = O d q -> c = d
shiftIsEqual Z Z b q p = Refl
shiftIsEqual Z (S d) b q p impossible
shiftIsEqual (S c) Z b q p impossible
shiftIsEqual (S c) (S d) b q p with (decEq b q)
  shiftIsEqual (S c) (S d) b q p | Yes prf =
    let
      (scEqsd, _) = O_injective p
    in
    scEqsd
  shiftIsEqual (S c) (S d) b q p | No contra =
    let
      brokenEq : ((S c = S d), (b = q))
      brokenEq = O_injective p
    in
    let
      (_, eqTail) = brokenEq
    in
    absurd (contra eqTail)

public export
canEqualizeShift : (c : Nat) -> (d : Nat) -> (b : Bin) -> (q : Bin) -> (O c b = O d q) -> (O c b = O c q)
canEqualizeShift c d b q p =
  let
    brokenProof : ((c = d), (b = q))
    brokenProof = O_injective p
  in
  let
    (shiftEq, tailEq) = brokenProof
  in
  O_bijective Refl tailEq

public export
xEqYMeansBin2NatXEqBin2NatY : (x : Bin) -> (y : Bin) -> (x = y) -> (bin2Nat x = bin2Nat y)
xEqYMeansBin2NatXEqBin2NatY BNil BNil p = Refl
xEqYMeansBin2NatXEqBin2NatY (O s t) BNil p =
  absurd (oNotBNil p)
xEqYMeansBin2NatXEqBin2NatY BNil (O u v) p =
  absurd (bnilNotO u v p)
xEqYMeansBin2NatXEqBin2NatY (O s t) (O u v) p =
  rewrite p in
  Refl

public export
tailNotMatch : (u : Nat) -> (v : Bin) -> O 0 (O u v) = O 0 BNil -> Void
tailNotMatch Z BNil p =
  let
    (shiftProof, tailProof) = O_injective p
  in
  absurd (oNotBNil tailProof)
tailNotMatch (S u) BNil p =
  let
    (shiftProof, tailProof) = O_injective p
  in
  absurd (oNotBNil tailProof)
tailNotMatch Z (O x y) p =
  let
    (shiftProof, tailProof) = O_injective p
  in
  absurd (oNotBNil tailProof)
tailNotMatch (S u) (O x y) p =
  let
    (shiftProof, tailProof) = O_injective p
  in
  absurd (oNotBNil tailProof)

public export
oneMoreFlipFromLeftGreaterThanOne : (n : Nat) -> (b : Bin) -> (oneMore (flipFromLeft (O n b)) = O 0 BNil) -> Void
oneMoreFlipFromLeftGreaterThanOne Z BNil p =
  let
    (shiftProof, tailProof) = O_injective p
  in
  absurd (sNotZ shiftProof)
oneMoreFlipFromLeftGreaterThanOne Z (O u v) p with (oneMore (flipFromLeft (O u v)))
  oneMoreFlipFromLeftGreaterThanOne Z (O u v) p | BNil = bnilNotO 0 BNil p
  oneMoreFlipFromLeftGreaterThanOne Z (O u v) p | (O e f) =
    let
      (shiftProof, tailProof) = O_injective p
    in
    absurd (sNotZ shiftProof)
oneMoreFlipFromLeftGreaterThanOne (S n) BNil p =
  let
    (shiftProof, tailProof) = O_injective p
  in
  absurd (sNotZ shiftProof)
oneMoreFlipFromLeftGreaterThanOne (S n) (O u v) p =
  let
    (shiftProof, tailProof) = O_injective p
  in
  absurd (sNotZ shiftProof)

mutual
  public export
  flipFromLeftNotBNil : (n : Nat) -> (b : Bin) -> flipFromLeft (O n b) = BNil -> Void
  flipFromLeftNotBNil Z BNil p = absurd (oNotBNil p)
  flipFromLeftNotBNil Z (O u v) p =
    absurd (oneMoreFlipFromLeftGreaterThanZero u v p)
  flipFromLeftNotBNil (S n) b p =
    absurd (oNotBNil p)

  public export
  oneMoreFlipFromLeftGreaterThanZero : (n : Nat) -> (b : Bin) -> (oneMore (flipFromLeft (O n b)) = BNil) -> Void
  oneMoreFlipFromLeftGreaterThanZero Z BNil p =
    absurd (oNotBNil p)
  oneMoreFlipFromLeftGreaterThanZero Z (O e f) p with (decEq (flipFromLeft (O e f)) BNil)
    oneMoreFlipFromLeftGreaterThanZero Z (O e f) p | Yes prf =
      absurd (flipFromLeftNotBNil e f prf)
    oneMoreFlipFromLeftGreaterThanZero Z (O e f) p | No contra =
      let
        bprf : (BNil = oneMore BNil)
        bprf = Refl

        p1 : (oneMore (oneMore (flipFromLeft (O e f))) = oneMore BNil)
        p1 =
          rewrite bprf in
          p

        p2 : (oneMore (flipFromLeft (O e f)) = BNil)
        p2 = oneMoreYEq (oneMore (flipFromLeft (O e f))) BNil p1

        p3 : (oneMore (flipFromLeft (O e f)) = oneMore BNil)
        p3 =
          rewrite bprf in
          p2

        p4 : flipFromLeft (O e f) = BNil
        p4 = oneMoreYEq (flipFromLeft (O e f)) BNil p3
      in
      absurd (flipFromLeftNotBNil e f p4)
  oneMoreFlipFromLeftGreaterThanZero (S n) BNil p =
    absurd (oNotBNil p)
  oneMoreFlipFromLeftGreaterThanZero (S n) (O e f) p =
    absurd (oNotBNil p)

  public export
  binIncUVNotEqO0BNil : (u : Nat) -> (v : Bin) -> (binInc (O u v) = O 0 BNil) -> Void
  binIncUVNotEqO0BNil Z BNil p impossible
  binIncUVNotEqO0BNil Z (O e f) p =
    absurd (oneMoreFlipFromLeftGreaterThanOne e f p)
  binIncUVNotEqO0BNil (S u) BNil p = tailNotMatch u BNil p
  binIncUVNotEqO0BNil (S u) (O g h) p = tailNotMatch u (O g h) p

  public export
  binIncCantYieldZero : (b : Bin) -> (binInc b = BNil) -> Void
  binIncCantYieldZero BNil p = oNotBNil p
  binIncCantYieldZero (O Z BNil) p = oNotBNil p
  binIncCantYieldZero (O Z (O e f)) p =
    absurd (oneMoreFlipFromLeftGreaterThanZero e f p)
  binIncCantYieldZero (O (S x) y) p = oNotBNil p

  public export
  binIncBNilEqOZBNil : binInc BNil = O Z BNil
  binIncBNilEqOZBNil = Refl

  public export
  binIncCantBeOne : (n : Nat) -> (b : Bin) -> binInc (O n b) = O Z BNil -> Void
  binIncCantBeOne Z BNil p =
    let
      (shiftProof, tailProof) = O_injective p
    in
    absurd (sNotZ shiftProof)
  binIncCantBeOne Z (O x y) p =
    absurd (oneMoreFlipFromLeftGreaterThanOne x y p)
  binIncCantBeOne (S n) BNil p =
    let
      (shiftProof, tailProof) = O_injective p
    in
    absurd (oNotBNil tailProof)
  binIncCantBeOne (S n) (O x y) p =
    let
      (shiftProof, tailProof) = O_injective p
    in
    absurd (oNotBNil tailProof)

  public export
  flipFromLeftNeverZero : (n : Nat) -> (b : Bin) -> flipFromLeft (O n b) = BNil -> Void
  flipFromLeftNeverZero Z BNil p = absurd (oNotBNil p)
  flipFromLeftNeverZero Z (O x y) p =
    absurd (oneMoreFlipFromLeftGreaterThanZero x y p)
  flipFromLeftNeverZero (S n) BNil p = absurd (oNotBNil p)
  flipFromLeftNeverZero (S n) (O x y) p = absurd (oNotBNil p)

  public export
  binIncZeroIsO0BNil : (b : Bin) -> binInc b = O 0 BNil -> b = BNil
  binIncZeroIsO0BNil BNil p = Refl
  binIncZeroIsO0BNil (O a x) p = absurd (binIncCantBeOne a x p)

  public export
  canRemoveBinInc1 : (s : Nat) -> (t : Bin) -> (u : Nat) -> (v : Bin) -> (e : Nat) -> (f : Bin) -> (binInc (O s t) = binInc (O u v)) -> (O e f = binInc (O s t)) -> (O e f = binInc (O u v))
  canRemoveBinInc1 s t u v Z BNil p lp =
    absurd (binIncCantBeOne s t (reverseProof lp))
  canRemoveBinInc1 Z BNil Z v Z (O x y) p lp =
    let
      (shiftProof, tailProof) = O_injective lp
    in
    absurd (zNotS shiftProof)
  canRemoveBinInc1 Z BNil (S u) v Z (O x y) p lp =
    let
      (shiftProof, tailProof) = O_injective lp
    in
    absurd (zNotS shiftProof)
  canRemoveBinInc1 Z (O Z t1) Z BNil Z (O x y) p lp =
    let
      p1 : (O 0 (O x y) = O 1 BNil)
      p1 =
        rewrite lp in
        p
    in
    let
      (shiftProof, tailProof) = O_injective p1
    in
    absurd (zNotS shiftProof)
  canRemoveBinInc1 Z (O (S t0) t1) Z BNil Z (O x y) p lp =
    let
      (shiftProof, tailProof) = O_injective lp
    in
    absurd (zNotS shiftProof)
  canRemoveBinInc1 Z (O t0 t1) Z (O v0 v1) Z (O x y) p lp =
    rewrite lp in
    p
  canRemoveBinInc1 Z (O t0 t1) (S u) v Z (O x y) p lp =
    rewrite lp in
    p
  canRemoveBinInc1 (S s) BNil u v Z (O x y) p lp =
    rewrite lp in
    p
  canRemoveBinInc1 (S s) (O t0 t1) u v Z (O x y) p lp =
    rewrite lp in
    p
  canRemoveBinInc1 s t u v (S e) f p lp =
    rewrite lp in
    p

  public export
  oneMoreShiftsOne : (b : Bin) -> (v : Bin) -> (O 1 b = oneMore v) -> (O 0 b = v)
  oneMoreShiftsOne BNil BNil p =
    absurd (oNotBNil p)
  oneMoreShiftsOne BNil (O Z y) p =
    let
      (_, tailProof) = O_injective p
    in
    rewrite tailProof in
    Refl
  oneMoreShiftsOne BNil (O (S x) y) p =
    let
      (shiftProof, tailProof) = O_injective p
    in
    absurd (zNotS (eqs Z (S x) shiftProof))
  oneMoreShiftsOne (O e f) v p =
    let
      p1 : (oneMore (O 0 (O e f)) = O 1 (O e f))
      p1 = Refl

      p2 : (oneMore (O 0 (O e f)) = oneMore v)
      p2 =
        rewrite p1 in
        p

      p3 : (O 0 (O e f) = v)
      p3 = oneMoreYEq (O 0 (O e f)) v p2
    in
    p3

  oneMoreNotZeroShift : (b : Bin) -> (v : Bin) -> (O 0 b = oneMore v) -> Void
  oneMoreNotZeroShift b BNil p =
    absurd (oNotBNil p)
  oneMoreNotZeroShift b (O x y) p =
    let
      (shiftProof, _) = O_injective p
    in
    absurd (zNotS shiftProof)

  flipFromLeftGtrZeroNotOne : (t0 : Nat) -> (t1 : Bin) -> (O Z BNil = flipFromLeft (O t0 t1)) -> Void
  flipFromLeftGtrZeroNotOne Z t1 p =
    absurd (oneMoreNotZeroShift BNil (flipFromLeft t1) p)
  flipFromLeftGtrZeroNotOne (S t0) t1 p =
    let
      (_, tailProof) = O_injective p
    in
    bnilNotO t0 t1 tailProof

  public export
  canRemoveFlipFromLeft : (b : Bin) -> (v : Bin) -> flipFromLeft b = flipFromLeft v -> b = v
  canRemoveFlipFromLeft BNil BNil p =
    Refl
  canRemoveFlipFromLeft BNil (O x y) p =
    absurd (flipFromLeftGtrZeroNotOne x y p)
  canRemoveFlipFromLeft (O e f) BNil p =
    absurd (flipFromLeftGtrZeroNotOne e f (reverseProof p))
  canRemoveFlipFromLeft (O Z f) (O Z y) p =
    let
      p1 : (flipFromLeft f = flipFromLeft y)
      p1 = oneMoreYEq (flipFromLeft f) (flipFromLeft y) p

      fEqY : (f = y)
      fEqY = canRemoveFlipFromLeft f y p1

      finalProof : (O 0 f = O 0 y)
      finalProof = O_bijective Refl fEqY
    in
    finalProof
  canRemoveFlipFromLeft (O Z f) (O (S x) y) p =
    absurd (oneMoreNotZeroShift (O x y) (flipFromLeft f) (reverseProof p))
  canRemoveFlipFromLeft (O (S e) f) (O Z y) p =
    absurd (oneMoreNotZeroShift (O e f) (flipFromLeft y) p)
  canRemoveFlipFromLeft (O (S e) f) (O (S x) y) p =
    let
      (_, tailProof1) = O_injective p
      (eEqX, fEqY) = O_injective tailProof1
    in
    rewrite eEqX in
    rewrite fEqY in
    Refl

  public export
  canRemoveBinInc : (a : Bin) -> (b : Bin) -> (binInc a = binInc b) -> (a = b)
  canRemoveBinInc BNil BNil p = Refl
  canRemoveBinInc BNil (O u v) p = absurd (binIncUVNotEqO0BNil u v (reverseProof p))
  canRemoveBinInc (O s t) BNil p = absurd (binIncUVNotEqO0BNil s t p)
  canRemoveBinInc (O Z BNil) (O Z BNil) p = Refl
  canRemoveBinInc (O Z BNil) (O Z (O Z BNil)) p =
    let
      (shiftProof, _) = O_injective p
    in
    absurd (oneIsNotTwo shiftProof)
  canRemoveBinInc (O Z BNil) (O Z (O Z (O x y))) p =
    let
      omProof : (O Z BNil = oneMore (flipFromLeft (O x y)))
      omProof = oneMoreShiftsOne BNil (oneMore (flipFromLeft (O x y))) p
    in
    absurd (oneMoreNotZeroShift BNil (flipFromLeft (O x y)) omProof)
  canRemoveBinInc (O Z BNil) (O Z (O (S v0) v1)) p =
    let
      (_, tailProof) = O_injective p
    in
    absurd (bnilNotO v0 v1 tailProof)
  canRemoveBinInc (O Z (O t0 t1)) (O Z BNil) p =
    let
      omProof : (O Z BNil = flipFromLeft (O t0 t1))
      omProof = oneMoreShiftsOne BNil (flipFromLeft (O t0 t1)) (reverseProof p)
    in
    absurd (flipFromLeftGtrZeroNotOne t0 t1 omProof)
  canRemoveBinInc (O Z (O t0 t1)) (O Z (O v0 v1)) p =
    let
      p1 : (flipFromLeft (O t0 t1) = flipFromLeft (O v0 v1))
      p1 = oneMoreYEq (flipFromLeft (O t0 t1)) (flipFromLeft (O v0 v1)) p

      p2 : (O t0 t1 = O v0 v1)
      p2 = canRemoveFlipFromLeft (O t0 t1) (O v0 v1) p1
    in
    rewrite p2 in
    Refl
  canRemoveBinInc (O Z (O t0 t1)) (O (S u) v) p =
    absurd (oneMoreNotZeroShift (O u v) (flipFromLeft (O t0 t1)) (reverseProof p))
  canRemoveBinInc (O Z BNil) (O (S u) v) p =
    let
      (shiftProof, _) = O_injective p
    in
    absurd (sNotZ shiftProof)
  canRemoveBinInc (O (S s) t) (O Z BNil) p =
    let
      (shiftProof, _) = O_injective p
    in
    absurd (zNotS shiftProof)
  canRemoveBinInc (O (S s) t) (O Z (O v0 v1)) p =
    absurd (oneMoreNotZeroShift (O s t) (flipFromLeft (O v0 v1)) p)
  canRemoveBinInc (O (S s) t) (O (S u) v) p =
    let
      (_, tailProof) = O_injective p
      (sEqU, tEqV) = O_injective tailProof
    in
    rewrite sEqU in
    rewrite tEqV in
    Refl

  public export
  canReduceO0WithBinInc : (n : Nat) -> (b : Bin) -> (O 0 (O n b) = binInc (O (S n) b))
  canReduceO0WithBinInc n b = Refl

  public export
  canReduceO1WithBinInc : (n : Nat) -> (b : Bin) -> (O 1 (O n b)) = oneMore (binInc (O (S n) b))
  canReduceO1WithBinInc Z b = Refl
  canReduceO1WithBinInc (S n) b = Refl

  public export
  oneMoreBinIncIs2Plus2X : (b : Bin) -> oneMore (binInc b) = binInc (binInc (oneMore b))
  oneMoreBinIncIs2Plus2X BNil = Refl
  oneMoreBinIncIs2Plus2X (O Z BNil) = Refl
  oneMoreBinIncIs2Plus2X (O Z (O x y)) = Refl
  oneMoreBinIncIs2Plus2X (O (S e) f) = Refl

  public export
  oZBIsBinIncN2BPlusBB : (b : Bin) -> O 0 b = binInc (nat2Bin (plus (bin2Nat b) (bin2Nat b)))
  oZBIsBinIncN2BPlusBB BNil = Refl
  oZBIsBinIncN2BPlusBB (O Z BNil) = Refl
  oZBIsBinIncN2BPlusBB (O Z (O Z y)) =
    rewrite sym (oneMoreXIs2X y) in
    rewrite sym (add2NEqNP2 (bin2Nat (oneMore y)) (bin2Nat (oneMore y))) in
    rewrite sym (add2NEqNP2 (plus (bin2Nat (oneMore y)) (bin2Nat (oneMore y))) (S (S (plus (bin2Nat (oneMore y)) (bin2Nat (oneMore y)))))) in
    rewrite sym (add2NEqNP2 (plus (bin2Nat (oneMore y)) (bin2Nat (oneMore y))) (S (plus (bin2Nat (oneMore y)) (bin2Nat (oneMore y))))) in
    rewrite sym (add2NEqNP2 (plus (bin2Nat (oneMore y)) (bin2Nat (oneMore y))) (plus (bin2Nat (oneMore y)) (bin2Nat (oneMore y)))) in
    rewrite sym (oneMoreXIs2X (oneMore y)) in
    rewrite sym (oneMoreXIs2X (oneMore (oneMore y))) in
    let
      p2 : (binInc (O 1 (O 0 y)) = (O 0 (O 0 (O 0 y))))
      p2 = canReduceO0WithBinInc Z (O 0 y)

      p3 : (oneMore (binInc (O 1 y)) = (O 1 (O 0 y)))
      p3 = canReduceO1WithBinInc Z y

      p4 : (binInc (oneMore (binInc (O 1 y))) = (O 0 (O 0 (O 0 y))))
      p4 =
        rewrite p2 in
        Refl

      p5 : (oneMore (binInc (O 1 y)) = binInc (binInc (oneMore (O 1 y))))
      p5 = oneMoreBinIncIs2Plus2X (O 1 y)

      p6 : (binInc (binInc (binInc (oneMore (O 1 y)))) = (O 0 (O 0 (O 0 y))))
      p6 =
        rewrite p4 in
        Refl

      p7 : (binInc (binInc (binInc (oneMore (oneMore (O 0 y))))) = (O 0 (O 0 (O 0 y))))
      p7 = Refl

      p8 : (O 0 y = binInc (oneMore y))
      p8 = reverseProof (binIncOneMoreIsO0 y)

      p9 : (binInc (binInc (binInc (oneMore (oneMore (binInc (oneMore y)))))) = (O 0 (O 0 (O 0 y))))
      p9 =
        rewrite p7 in
        rewrite p8 in
        rewrite sym (canReduceO0WithBinInc 0 (binInc (oneMore y))) in
        rewrite sym p8 in
        Refl
    in
    rewrite sym p9 in
    rewrite oneMoreBinIncIs2Plus2X (oneMore y) in
    rewrite oneMoreBinIncIs2Plus2X (binInc (oneMore (oneMore y))) in
    rewrite oneMoreBinIncIs2Plus2X (oneMore (oneMore y)) in
    rewrite sym (assert_total (nat2BinIsReflexiveWithBin2Nat (oneMore (oneMore (oneMore y))))) in
    Refl

  oZBIsBinIncN2BPlusBB (O Z (O (S x) y)) =
    let
      p1 : (O 0 (O 0 (O (S x) y)) = binInc (binInc (binInc (oneMore (oneMore (oneMore (O x y)))))))
      p1 =
        Refl
    in
    rewrite p1 in
    rewrite sym (oneMoreXIs2X (O x y)) in
    rewrite sym (oneMoreXIs2X (oneMore (O x y))) in
    rewrite sym (add2NEqNP2 (bin2Nat (oneMore (oneMore (O x y)))) (bin2Nat (oneMore (oneMore (O x y))))) in
    rewrite sym (oneMoreXIs2X (oneMore (oneMore (O x y)))) in
    rewrite sym (assert_total (nat2BinIsReflexiveWithBin2Nat (oneMore (oneMore (oneMore (O x y)))))) in
    Refl

  oZBIsBinIncN2BPlusBB (O (S x) y) =
    let
      p1 : (O 0 (O (S x) y) = binInc (oneMore (oneMore (O x y))))
      p1 =
        Refl
    in
    rewrite p1 in
    rewrite sym (oneMoreXIs2X (O x y)) in
    rewrite sym (oneMoreXIs2X (oneMore (O x y))) in
    rewrite sym (assert_total (nat2BinIsReflexiveWithBin2Nat (oneMore (oneMore (O x y))))) in
    Refl

  public export
  oneMoreYEq : (y : Bin) -> (t : Bin) -> oneMore y = oneMore t -> y = t
  oneMoreYEq BNil BNil p = Refl
  oneMoreYEq BNil (O m y) Refl impossible
  oneMoreYEq (O s t) BNil Refl impossible
  oneMoreYEq (O Z t) (O Z y) p =
    rewrite oZBIsBinIncN2BPlusBB t in
    rewrite oZBIsBinIncN2BPlusBB y in
    rewrite sym (oneMoreXIs2X t) in
    rewrite sym (oneMoreXIs2X y) in
    rewrite sym (nat2BinIsReflexiveWithBin2Nat (oneMore t)) in
    rewrite sym (nat2BinIsReflexiveWithBin2Nat (oneMore y)) in
    rewrite collapseEqTail 1 1 t y p in
    Refl
  oneMoreYEq (O Z t) (O (S m) y) _ impossible
  oneMoreYEq (O (S s) t) (O Z y) p impossible
  oneMoreYEq (O (S s) h) (O (S m) i) p =
    let
      sie1x : (S (S s) = S (S m))
      sie1x = shiftIsEqual (S (S s)) (S (S m)) h i p

      sierw : (S s = S m)
      sierw = eqs (S s) (S m) sie1x

      sie2x : (O (S (S s)) h = O (S (S s)) i)
      sie2x = canEqualizeShift (S (S s)) (S (S m)) h i p

      sie3x : (O (S s) h = O (S s) i)
      sie3x = oneLessShift (S s) h i sie2x
    in
    rewrite sym sierw in
    sie3x

  public export
  revYMeansBin2NatXEqBin2NatY : (x : Bin) -> (y : Bin) -> (bin2Nat x = bin2Nat y) -> (x = y)
  revYMeansBin2NatXEqBin2NatY BNil BNil p = Refl
  revYMeansBin2NatXEqBin2NatY (O s t) BNil p =
    let
      p2 : (0 = bin2Nat (O s t))
      p2 = reverseProof p
    in
    absurd (bin2NatOIsNotBNil2 s t p2)
  revYMeansBin2NatXEqBin2NatY BNil (O u v) p =
    absurd (bin2NatOIsNotBNil2 u v p)
  revYMeansBin2NatXEqBin2NatY (O Z t) (O Z v) p =
    let
      p1 : (plus (bin2Nat t) (bin2Nat t) = plus (bin2Nat v) (bin2Nat v))
      p1 = eqs (plus (bin2Nat t) (bin2Nat t)) (plus (bin2Nat v) (bin2Nat v)) p

      p2 : (bin2Nat t = bin2Nat v)
      p2 = plusAAEqPlusBBMeansAEqB (bin2Nat t) (bin2Nat v) p1

      p3 : (t = v)
      p3 = revYMeansBin2NatXEqBin2NatY t v p2
    in
    rewrite p3 in
    Refl
  revYMeansBin2NatXEqBin2NatY (O Z t) (O (S u) v) p =
    let
      p4 : (S (plus (bin2Nat t) (bin2Nat t)) = plus (bin2Nat (O u v)) (bin2Nat (O u v))) -> Void
      p4 =
        oddNotEqualEven (bin2Nat t) (bin2Nat (O u v))
    in
    absurd (p4 p)
  revYMeansBin2NatXEqBin2NatY (O (S s) t) (O Z v) p =
    let
      p1 : (S (plus (bin2Nat v) (bin2Nat v)) = plus (bin2Nat (O s t)) (bin2Nat (O s t)))
      p1 = reverseProof p
    in
    absurd (oddNotEqualEven (bin2Nat v) (bin2Nat (O s t)) p1)
  revYMeansBin2NatXEqBin2NatY (O (S s) t) (O (S u) v) p =
    let
      p1 : (bin2Nat (O s t) = bin2Nat (O u v))
      p1 = plusAAEqPlusBBMeansAEqB (bin2Nat (O s t)) (bin2Nat (O u v)) p

      p2 : (O s t = O u v)
      p2 = assert_total (revYMeansBin2NatXEqBin2NatY (O s t) (O u v) p1)

      p3 : (s = u, t = v)
      p3 = O_injective p2
    in
    let
      (prfS, prfT) = p3
    in
    rewrite prfS in
    rewrite prfT in
    Refl

  public export
  bin2NatCanMove : (x : Bin) -> (a : Nat) -> bin2Nat x = a -> x = nat2Bin a
  bin2NatCanMove BNil Z p = Refl
  bin2NatCanMove BNil (S r) p = absurd (zNotS p)
  bin2NatCanMove (O b z) Z p =
    let
      rp : (bin2Nat (O b z) = 0) -> Void
      rp = bin2NatOIsNotBNil b z
    in
    absurd (rp p)
  bin2NatCanMove (O b z) (S r) p =
    let
      r1 : (bin2Nat (O b z) = bin2Nat (binInc (nat2Bin r)))
      r1 =
        rewrite sym (testBin2Nat (nat2Bin r)) in
        rewrite p in
        rewrite sym (bin2NatIsReflexiveWithNat2Bin r) in
        Refl

      p1 : (O b z = binInc (nat2Bin r))
      p1 = revYMeansBin2NatXEqBin2NatY (O b z) (binInc (nat2Bin r)) r1
    in
    p1

  public export
  nat2BinIsReflexiveWithBin2Nat : (b : Bin) -> b = (nat2Bin (bin2Nat b))
  nat2BinIsReflexiveWithBin2Nat BNil = Refl
  nat2BinIsReflexiveWithBin2Nat (O Z BNil) = Refl
  nat2BinIsReflexiveWithBin2Nat (O Z (O a x)) =
    rewrite oZBIsBinIncN2BPlusBB (O a x) in
    Refl
  nat2BinIsReflexiveWithBin2Nat (O (S v) z) =
    let
      p1 : (bin2Nat (O (S v) z) = plus (bin2Nat (O v z)) (bin2Nat (O v z)))
      p1 = plusOaxOaxIsOSax v z

      p2 : ((O (S v) z) = nat2Bin (plus (bin2Nat (O v z)) (bin2Nat (O v z))))
      p2 = bin2NatCanMove (O (S v) z) (plus (bin2Nat (O v z)) (bin2Nat (O v z))) p1
    in
    p2

binShrIsDiv2Nat : (b : Bin) -> binShr1 b = nat2Bin (div2Nat (bin2Nat b))
binShrIsDiv2Nat BNil = Refl
binShrIsDiv2Nat (O Z x) =
  rewrite div2NatOnePlusAPAIsA (bin2Nat x) in
  rewrite sym (nat2BinIsReflexiveWithBin2Nat x) in
  Refl
binShrIsDiv2Nat (O (S a) x) =
  rewrite div2NatPlusAAIsA (bin2Nat (O a x)) in
  rewrite sym (nat2BinIsReflexiveWithBin2Nat (O a x)) in
  Refl

public export
binAnd : (b : Bin) -> (c : Bin) -> Bin
binAnd BNil _ = BNil
binAnd _ BNil = BNil
binAnd (O Z c) (O Z v) = O Z (binAnd c v)
binAnd (O Z c) (O (S b) v) = binAnd (O (S b) v) (O Z c)
binAnd (O (S a) c) (O Z v) = oneMore (assert_total (binAnd (O a c) v))
binAnd (O (S a) c) (O (S b) v) = oneMore (assert_total (binAnd (O a c) (O b v)))

public export
binXor : (b : Bin) -> (c : Bin) -> Bin
binXor BNil b = b
binXor a BNil = a
binXor (O Z c) (O Z v) = O (S Z) (binXor c v)
binXor (O Z c) (O (S b) v) = O Z (assert_total (binXor c (O b v)))
binXor (O (S a) c) (O Z v) = O Z (assert_total (binXor v (O a c)))
binXor (O (S a) c) (O (S b) v) = oneMore (assert_total (binXor (O a c) (O b v)))

public export
binNot : (n : Nat) -> (b : Bin) -> Bin
binNot Z x = BNil
binNot (S n) BNil = O Z (binNot n BNil)
binNot (S n) (O Z v) = oneMore (binNot n v)
binNot (S n) (O (S b) v) = O Z (binNot n (O b v))

public export
binShl : (n : Nat) -> (b : Bin) -> Bin
binShl Z b = b
binShl (S n) b = binShl n (oneMore b)

public export
binShr : (n : Nat) -> (b : Bin) -> Bin
binShr Z b = b
binShr (S n) BNil = BNil
binShr (S n) (O Z v) = binShr n v
binShr (S n) (O (S b) v) = binShr n (O b v)

public export
binTrunc : (n : Nat) -> (b : Bin) -> Bin
binTrunc Z _ = BNil
binTrunc _ BNil = BNil
binTrunc (S n) (O Z v) = O Z (binTrunc n v)
binTrunc (S n) (O (S b) v) = oneMore (binTrunc n (O b v))

