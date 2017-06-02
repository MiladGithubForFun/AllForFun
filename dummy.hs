module Dummy where

import qualified Prelude


false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r x h y =
  eq_rect x h y

data Bool =
   True
 | False

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x y -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair x y -> y}

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons y l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

compOpp :: Prelude.Ordering -> Prelude.Ordering
compOpp r =
  case r of {
   Prelude.EQ -> Prelude.EQ;
   Prelude.LT -> Prelude.GT;
   Prelude.GT -> Prelude.LT}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Prelude.Ordering -> CompareSpecT
compareSpec2Type c =
  case c of {
   Prelude.EQ -> CompEqT;
   Prelude.LT -> CompLtT;
   Prelude.GT -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Prelude.Ordering -> CompSpecT a1
compSpec2Type x y c =
  compareSpec2Type c

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Sumor a =
   Inleft a
 | Inright

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

minus :: Nat -> Nat -> Nat
minus n m =
  case n of {
   O -> n;
   S k ->
    case m of {
     O -> n;
     S l -> minus k l}}

nat_iter :: Nat -> (a1 -> a1) -> a1 -> a1
nat_iter n f x =
  case n of {
   O -> x;
   S n' -> f (nat_iter n' f x)}

acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
acc_rect f x =
  f x __ (\y _ -> acc_rect f y)

well_founded_induction_type :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction_type x a =
  acc_rect (\x0 _ x1 -> x x0 x1) a

positive_rect :: (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1 ->
                 a1) -> a1 -> Prelude.Integer -> a1
positive_rect f f0 f1 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    f p0 (positive_rect f f0 f1 p0))
    (\p0 ->
    f0 p0 (positive_rect f f0 f1 p0))
    (\_ ->
    f1)
    p

positive_rec :: (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1 ->
                a1) -> a1 -> Prelude.Integer -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Prelude.Integer

n_rect :: a1 -> (Prelude.Integer -> a1) -> N -> a1
n_rect f f0 n =
  case n of {
   N0 -> f;
   Npos x -> f0 x}

n_rec :: a1 -> (Prelude.Integer -> a1) -> N -> a1
n_rec =
  n_rect

z_rect :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
          Prelude.Integer -> a1
z_rect f f0 f1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    f)
    (\x ->
    f0 x)
    (\x ->
    f1 x)
    z

z_rec :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
         Prelude.Integer -> a1
z_rec =
  z_rect

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Bool -> Reflect
iff_reflect b =
  case b of {
   True -> and_rec (\_ _ -> ReflectT);
   False -> and_rec (\_ _ -> ReflectF)}

type T = Prelude.Integer

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      ((Prelude.succ) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      ((Prelude.+) p q))
      (\_ -> (\x -> 2 Prelude.* x)
      ((Prelude.succ) p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      ((Prelude.succ) q))
      (\q -> (\x -> 2 Prelude.* x)
      ((Prelude.succ) q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    (pred_double p))
    (\_ ->
    1)
    x

pred_N :: Prelude.Integer -> N
pred_N x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> Npos ((\x -> 2 Prelude.* x)
    p))
    (\p -> Npos
    (pred_double p))
    (\_ ->
    N0)
    x

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

mask_rect :: a1 -> (Prelude.Integer -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos x -> f0 x;
   IsNeg -> f1}

mask_rec :: a1 -> (Prelude.Integer -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos ((\x -> 2 Prelude.* x Prelude.+ 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((\x -> 2 Prelude.* x) p);
   x0 -> x0}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p -> IsPos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    p)))
    (\p -> IsPos ((\x -> 2 Prelude.* x)
    (pred_double p)))
    (\_ ->
    IsNul)
    x

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> IsPos
      ((Prelude.pred) q))
      (\p0 -> IsPos
      ((Prelude.pred) q))
      (\_ ->
      IsNul)
      q;
   _ -> IsNeg}

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask p q))
      (\q ->
      succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> 2 Prelude.* x)
      p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p ->
      IsNeg)
      (\p ->
      IsNeg)
      (\_ ->
      IsNul)
      y)
    x

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask_carry p q))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\_ ->
      double_pred_mask p)
      y)
    (\_ ->
    IsNeg)
    x

iter :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter n f x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\n' ->
    f (iter n' f (iter n' f x)))
    (\n' ->
    iter n' f (iter n' f x))
    (\_ ->
    f x)
    n

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow x y =
  iter y ((Prelude.*) x) 1

square :: Prelude.Integer -> Prelude.Integer
square p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((Prelude.+) (square p0) p0)))
    (\p0 -> (\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    (square p0)))
    (\_ ->
    1)
    p

div2 :: Prelude.Integer -> Prelude.Integer
div2 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    p0)
    (\p0 ->
    p0)
    (\_ ->
    1)
    p

div2_up :: Prelude.Integer -> Prelude.Integer
div2_up p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (Prelude.succ) p0)
    (\p0 ->
    p0)
    (\_ ->
    1)
    p

size_nat :: Prelude.Integer -> Nat
size_nat p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 -> S
    (size_nat p0))
    (\p0 -> S
    (size_nat p0))
    (\_ -> S
    O)
    p

size :: Prelude.Integer -> Prelude.Integer
size p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (Prelude.succ) (size p0))
    (\p0 ->
    (Prelude.succ) (size p0))
    (\_ ->
    1)
    p

compare_cont :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering ->
                Prelude.Ordering
compare_cont x y r =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont p q r)
      (\q ->
      compare_cont p q Prelude.GT)
      (\_ ->
      Prelude.GT)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont p q Prelude.LT)
      (\q ->
      compare_cont p q r)
      (\_ ->
      Prelude.GT)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      Prelude.LT)
      (\q ->
      Prelude.LT)
      (\_ ->
      r)
      y)
    x

eqb :: Prelude.Integer -> Prelude.Integer -> Bool
eqb p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      eqb p0 q0)
      (\p1 ->
      False)
      (\_ ->
      False)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p1 ->
      False)
      (\q0 ->
      eqb p0 q0)
      (\_ ->
      False)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      False)
      (\p0 ->
      False)
      (\_ ->
      True)
      q)
    p

leb :: Prelude.Integer -> Prelude.Integer -> Bool
leb x y =
  case (Prelude.compare) x y of {
   Prelude.GT -> False;
   _ -> True}

ltb :: Prelude.Integer -> Prelude.Integer -> Bool
ltb x y =
  case (Prelude.compare) x y of {
   Prelude.LT -> True;
   _ -> False}

sqrtrem_step :: (Prelude.Integer -> Prelude.Integer) -> (Prelude.Integer ->
                Prelude.Integer) -> (Prod Prelude.Integer Mask) -> Prod
                Prelude.Integer Mask
sqrtrem_step f g p =
  case p of {
   Pair s y ->
    case y of {
     IsPos r ->
      let {s' = (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) s)}
      in
      let {r' = g (f r)} in
      case leb s' r' of {
       True -> Pair ((\x -> 2 Prelude.* x Prelude.+ 1) s) (sub_mask r' s');
       False -> Pair ((\x -> 2 Prelude.* x) s) (IsPos r')};
     _ -> Pair ((\x -> 2 Prelude.* x) s)
      (sub_mask (g (f 1)) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))}}

sqrtrem :: Prelude.Integer -> Prod Prelude.Integer Mask
sqrtrem p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p1 ->
      sqrtrem_step (\x -> (\x -> 2 Prelude.* x Prelude.+ 1) x) (\x ->
        (\x -> 2 Prelude.* x Prelude.+ 1) x) (sqrtrem p1))
      (\p1 ->
      sqrtrem_step (\x -> (\x -> 2 Prelude.* x) x) (\x ->
        (\x -> 2 Prelude.* x Prelude.+ 1) x) (sqrtrem p1))
      (\_ -> Pair 1 (IsPos ((\x -> 2 Prelude.* x)
      1)))
      p0)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p1 ->
      sqrtrem_step (\x -> (\x -> 2 Prelude.* x Prelude.+ 1) x) (\x ->
        (\x -> 2 Prelude.* x) x) (sqrtrem p1))
      (\p1 ->
      sqrtrem_step (\x -> (\x -> 2 Prelude.* x) x) (\x ->
        (\x -> 2 Prelude.* x) x) (sqrtrem p1))
      (\_ -> Pair 1 (IsPos
      1))
      p0)
    (\_ -> Pair 1
    IsNul)
    p

sqrt :: Prelude.Integer -> Prelude.Integer
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcdn n a b =
  case n of {
   O -> 1;
   S n0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\a' ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\b' ->
        case (Prelude.compare) a' b' of {
         Prelude.EQ -> a;
         Prelude.LT -> gcdn n0 ((Prelude.-) b' a') a;
         Prelude.GT -> gcdn n0 ((Prelude.-) a' b') b})
        (\b0 ->
        gcdn n0 a b0)
        (\_ ->
        1)
        b)
      (\a0 ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\p ->
        gcdn n0 a0 b)
        (\b0 -> (\x -> 2 Prelude.* x)
        (gcdn n0 a0 b0))
        (\_ ->
        1)
        b)
      (\_ ->
      1)
      a}

gcd :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd a b =
  gcdn (plus (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
         (Prod Prelude.Integer Prelude.Integer)
ggcdn n a b =
  case n of {
   O -> Pair 1 (Pair a b);
   S n0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\a' ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\b' ->
        case (Prelude.compare) a' b' of {
         Prelude.EQ -> Pair a (Pair 1 1);
         Prelude.LT ->
          case ggcdn n0 ((Prelude.-) b' a') a of {
           Pair g p ->
            case p of {
             Pair ba aa -> Pair g (Pair aa
              ((Prelude.+) aa ((\x -> 2 Prelude.* x) ba)))}};
         Prelude.GT ->
          case ggcdn n0 ((Prelude.-) a' b') b of {
           Pair g p ->
            case p of {
             Pair ab bb -> Pair g (Pair
              ((Prelude.+) bb ((\x -> 2 Prelude.* x) ab)) bb)}}})
        (\b0 ->
        case ggcdn n0 a b0 of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair aa ((\x -> 2 Prelude.* x) bb))}})
        (\_ -> Pair 1 (Pair a
        1))
        b)
      (\a0 ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\p ->
        case ggcdn n0 a0 b of {
         Pair g p0 ->
          case p0 of {
           Pair aa bb -> Pair g (Pair ((\x -> 2 Prelude.* x) aa) bb)}})
        (\b0 ->
        case ggcdn n0 a0 b0 of {
         Pair g p -> Pair ((\x -> 2 Prelude.* x) g) p})
        (\_ -> Pair 1 (Pair a
        1))
        b)
      (\_ -> Pair 1 (Pair 1
      b))
      a}

ggcd :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
        (Prod Prelude.Integer Prelude.Integer)
ggcd a b =
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos 1;
   Npos p -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos ((\x -> 2 Prelude.* x) p)}

lor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (lor p0 q0))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (lor p0 q0))
      (\_ ->
      p)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (lor p0 q0))
      (\q0 -> (\x -> 2 Prelude.* x)
      (lor p0 q0))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      p0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      q)
      (\q0 -> (\x -> 2 Prelude.* x Prelude.+ 1)
      q0)
      (\_ ->
      q)
      q)
    p

land :: Prelude.Integer -> Prelude.Integer -> N
land p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      nsucc_double (land p0 q0))
      (\q0 ->
      ndouble (land p0 q0))
      (\_ -> Npos
      1)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (land p0 q0))
      (\q0 ->
      ndouble (land p0 q0))
      (\_ ->
      N0)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> Npos
      1)
      (\q0 ->
      N0)
      (\_ -> Npos
      1)
      q)
    p

ldiff :: Prelude.Integer -> Prelude.Integer -> N
ldiff p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\q0 ->
      nsucc_double (ldiff p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x)
      p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\_ -> Npos
      p)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      N0)
      (\q0 -> Npos
      1)
      (\_ ->
      N0)
      q)
    p

lxor :: Prelude.Integer -> Prelude.Integer -> N
lxor p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      ndouble (lxor p0 q0))
      (\q0 ->
      nsucc_double (lxor p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x)
      p0))
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 ->
      nsucc_double (lxor p0 q0))
      (\q0 ->
      ndouble (lxor p0 q0))
      (\_ -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1)
      p0))
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q0 -> Npos ((\x -> 2 Prelude.* x)
      q0))
      (\q0 -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1)
      q0))
      (\_ ->
      N0)
      q)
    p

shiftl_nat :: Prelude.Integer -> Nat -> Prelude.Integer
shiftl_nat p n =
  nat_iter n (\x -> (\x -> 2 Prelude.* x) x) p

shiftr_nat :: Prelude.Integer -> Nat -> Prelude.Integer
shiftr_nat p n =
  nat_iter n div2 p

shiftl :: Prelude.Integer -> N -> Prelude.Integer
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 (\x -> (\x -> 2 Prelude.* x) x) p}

shiftr :: Prelude.Integer -> N -> Prelude.Integer
shiftr p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 div2 p}

testbit_nat :: Prelude.Integer -> Nat -> Bool
testbit_nat p n =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    case n of {
     O -> True;
     S n' -> testbit_nat p0 n'})
    (\p0 ->
    case n of {
     O -> False;
     S n' -> testbit_nat p0 n'})
    (\_ ->
    case n of {
     O -> True;
     S n0 -> False})
    p

testbit :: Prelude.Integer -> N -> Bool
testbit p n =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    case n of {
     N0 -> True;
     Npos n0 -> testbit p0 (pred_N n0)})
    (\p0 ->
    case n of {
     N0 -> False;
     Npos n0 -> testbit p0 (pred_N n0)})
    (\_ ->
    case n of {
     N0 -> True;
     Npos p0 -> False})
    p

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    op a (iter_op op p0 (op a a)))
    (\p0 ->
    iter_op op p0 (op a a))
    (\_ ->
    a)
    p

to_nat :: Prelude.Integer -> Nat
to_nat x =
  iter_op plus x (S O)

of_nat :: Nat -> Prelude.Integer
of_nat n =
  case n of {
   O -> 1;
   S x ->
    case x of {
     O -> 1;
     S n0 -> (Prelude.succ) (of_nat x)}}

of_succ_nat :: Nat -> Prelude.Integer
of_succ_nat n =
  case n of {
   O -> 1;
   S x -> (Prelude.succ) (of_succ_nat x)}

eq_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec x y =
  positive_rec (\p h y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0))
      (\p0 ->
      Right)
      (\_ ->
      Right)
      y0) (\p h y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      Right)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0))
      (\_ ->
      Right)
      y0) (\y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p ->
      Right)
      (\p ->
      Right)
      (\_ ->
      Left)
      y0) x y

peano_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
peano_rect a f p =
  let {
   f2 = peano_rect (f 1 a) (\p0 x ->
          f ((Prelude.succ) ((\x -> 2 Prelude.* x) p0))
            (f ((\x -> 2 Prelude.* x) p0) x))}
  in
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\q ->
    f ((\x -> 2 Prelude.* x) q) (f2 q))
    (\q ->
    f2 q)
    (\_ ->
    a)
    p

peano_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Prelude.Integer PeanoView

peanoView_rect :: a1 -> (Prelude.Integer -> PeanoView -> a1 -> a1) ->
                  Prelude.Integer -> PeanoView -> a1
peanoView_rect f f0 p p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p1 p2 -> f0 p1 p2 (peanoView_rect f f0 p1 p2)}

peanoView_rec :: a1 -> (Prelude.Integer -> PeanoView -> a1 -> a1) ->
                 Prelude.Integer -> PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Prelude.Integer -> PeanoView -> PeanoView
peanoView_xO p q =
  case q of {
   PeanoOne -> PeanoSucc 1 PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc ((Prelude.succ) ((\x -> 2 Prelude.* x) p0))
    (PeanoSucc ((\x -> 2 Prelude.* x) p0) (peanoView_xO p0 q0))}

peanoView_xI :: Prelude.Integer -> PeanoView -> PeanoView
peanoView_xI p q =
  case q of {
   PeanoOne -> PeanoSucc ((Prelude.succ) 1) (PeanoSucc 1 PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc
    ((Prelude.succ) ((\x -> 2 Prelude.* x Prelude.+ 1) p0)) (PeanoSucc
    ((\x -> 2 Prelude.* x Prelude.+ 1) p0) (peanoView_xI p0 q0))}

peanoView :: Prelude.Integer -> PeanoView
peanoView p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p0 ->
    peanoView_xI p0 (peanoView p0))
    (\p0 ->
    peanoView_xO p0 (peanoView p0))
    (\_ ->
    PeanoOne)
    p

peanoView_iter :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer ->
                  PeanoView -> a1
peanoView_iter a f p q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Prelude.Integer -> Prelude.Integer -> Reflect
eqb_spec x y =
  iff_reflect (eqb x y)

switch_Eq :: Prelude.Ordering -> Prelude.Ordering -> Prelude.Ordering
switch_Eq c c' =
  case c' of {
   Prelude.EQ -> c;
   x -> x}

mask2cmp :: Mask -> Prelude.Ordering
mask2cmp p =
  case p of {
   IsNul -> Prelude.EQ;
   IsPos p0 -> Prelude.GT;
   IsNeg -> Prelude.LT}

leb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec0 x y =
  iff_reflect (leb x y)

ltb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb x y)

max_case_strong :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                   Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (() ->
                   a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m ((Prelude.compare) n m)} in
  case c of {
   CompGtT -> compat n ((Prelude.max) n m) __ (hl __);
   _ -> compat m ((Prelude.max) n m) __ (hr __)}

max_case :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
            Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec n m =
  max_case n m (\x y _ h0 -> h0) Left Right

min_case_strong :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                   Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (() ->
                   a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m ((Prelude.compare) n m)} in
  case c of {
   CompGtT -> compat m ((Prelude.min) n m) __ (hr __);
   _ -> compat n ((Prelude.min) n m) __ (hl __)}

min_case :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
            Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec n m =
  min_case n m (\x y _ h0 -> h0) Left Right

max_case_strong0 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case0 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec0 =
  max_dec

min_case_strong0 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case0 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec0 =
  min_dec

type T0 = N

zero :: N
zero =
  N0

one :: N
one =
  Npos 1

two :: N
two =
  Npos ((\x -> 2 Prelude.* x) 1)

succ_double :: N -> N
succ_double x =
  case x of {
   N0 -> Npos 1;
   Npos p -> Npos ((\x -> 2 Prelude.* x Prelude.+ 1) p)}

double :: N -> N
double n =
  case n of {
   N0 -> N0;
   Npos p -> Npos ((\x -> 2 Prelude.* x) p)}

succ :: N -> N
succ n =
  case n of {
   N0 -> Npos 1;
   Npos p -> Npos ((Prelude.succ) p)}

pred :: N -> N
pred n =
  case n of {
   N0 -> N0;
   Npos p -> pred_N p}

succ_pos :: N -> Prelude.Integer
succ_pos n =
  case n of {
   N0 -> 1;
   Npos p -> (Prelude.succ) p}

add :: N -> N -> N
add n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos ((Prelude.+) p q)}}

sub :: N -> N -> N
sub n m =
  case n of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n;
     Npos m' ->
      case sub_mask n' m' of {
       IsPos p -> Npos p;
       _ -> N0}}}

mul :: N -> N -> N
mul n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> Npos ((Prelude.*) p q)}}

compare :: N -> N -> Prelude.Ordering
compare n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Prelude.EQ;
     Npos m' -> Prelude.LT};
   Npos n' ->
    case m of {
     N0 -> Prelude.GT;
     Npos m' -> (Prelude.compare) n' m'}}

eqb0 :: N -> N -> Bool
eqb0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> True;
     Npos p -> False};
   Npos p ->
    case m of {
     N0 -> False;
     Npos q -> eqb p q}}

leb0 :: N -> N -> Bool
leb0 x y =
  case compare x y of {
   Prelude.GT -> False;
   _ -> True}

ltb0 :: N -> N -> Bool
ltb0 x y =
  case compare x y of {
   Prelude.LT -> True;
   _ -> False}

min :: N -> N -> N
min n n' =
  case compare n n' of {
   Prelude.GT -> n';
   _ -> n}

max :: N -> N -> N
max n n' =
  case compare n n' of {
   Prelude.GT -> n;
   _ -> n'}

div0 :: N -> N
div0 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p -> Npos
      p)
      (\p -> Npos
      p)
      (\_ ->
      N0)
      p0}

even :: N -> Bool
even n =
  case n of {
   N0 -> True;
   Npos p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      False)
      (\p0 ->
      True)
      (\_ ->
      False)
      p}

odd :: N -> Bool
odd n =
  negb (even n)

pow0 :: N -> N -> N
pow0 n p =
  case p of {
   N0 -> Npos 1;
   Npos p0 ->
    case n of {
     N0 -> N0;
     Npos q -> Npos (pow q p0)}}

square0 :: N -> N
square0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (square p)}

log2 :: N -> N
log2 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p -> Npos
      (size p))
      (\p -> Npos
      (size p))
      (\_ ->
      N0)
      p0}

size0 :: N -> N
size0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (size p)}

size_nat0 :: N -> Nat
size_nat0 n =
  case n of {
   N0 -> O;
   Npos p -> size_nat p}

pos_div_eucl :: Prelude.Integer -> N -> Prod N N
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub r' b);
       False -> Pair (double q) r'}})
    (\a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub r' b);
       False -> Pair (double q) r'}})
    (\_ ->
    case b of {
     N0 -> Pair N0 (Npos 1);
     Npos p ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
        (\p0 -> Pair N0 (Npos
        1))
        (\p0 -> Pair N0 (Npos
        1))
        (\_ -> Pair (Npos 1)
        N0)
        p})
    a

div_eucl :: N -> N -> Prod N N
div_eucl a b =
  case a of {
   N0 -> Pair N0 N0;
   Npos na ->
    case b of {
     N0 -> Pair N0 a;
     Npos p -> pos_div_eucl na b}}

div :: N -> N -> N
div a b =
  fst (div_eucl a b)

modulo :: N -> N -> N
modulo a b =
  snd (div_eucl a b)

gcd0 :: N -> N -> N
gcd0 a b =
  case a of {
   N0 -> b;
   Npos p ->
    case b of {
     N0 -> a;
     Npos q -> Npos (gcd p q)}}

ggcd0 :: N -> N -> Prod N (Prod N N)
ggcd0 a b =
  case a of {
   N0 -> Pair b (Pair N0 (Npos 1));
   Npos p ->
    case b of {
     N0 -> Pair a (Pair (Npos 1) N0);
     Npos q ->
      case ggcd p q of {
       Pair g p0 ->
        case p0 of {
         Pair aa bb -> Pair (Npos g) (Pair (Npos aa) (Npos bb))}}}}

sqrtrem0 :: N -> Prod N N
sqrtrem0 n =
  case n of {
   N0 -> Pair N0 N0;
   Npos p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair (Npos s) (Npos r);
       _ -> Pair (Npos s) N0}}}

sqrt0 :: N -> N
sqrt0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (sqrt p)}

lor0 :: N -> N -> N
lor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> ldiff p q}}

lxor0 :: N -> N -> N
lxor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> lxor p q}}

shiftl_nat0 :: N -> Nat -> N
shiftl_nat0 a n =
  nat_iter n double a

shiftr_nat0 :: N -> Nat -> N
shiftr_nat0 a n =
  nat_iter n div0 a

shiftl0 :: N -> N -> N
shiftl0 a n =
  case a of {
   N0 -> N0;
   Npos a0 -> Npos (shiftl a0 n)}

shiftr0 :: N -> N -> N
shiftr0 a n =
  case n of {
   N0 -> a;
   Npos p -> iter p div0 a}

testbit_nat0 :: N -> Nat -> Bool
testbit_nat0 a =
  case a of {
   N0 -> (\x -> False);
   Npos p -> testbit_nat p}

testbit0 :: N -> N -> Bool
testbit0 a n =
  case a of {
   N0 -> False;
   Npos p -> testbit p n}

to_nat0 :: N -> Nat
to_nat0 a =
  case a of {
   N0 -> O;
   Npos p -> to_nat p}

of_nat0 :: Nat -> N
of_nat0 n =
  case n of {
   O -> N0;
   S n' -> Npos (of_succ_nat n')}

iter0 :: N -> (a1 -> a1) -> a1 -> a1
iter0 n f x =
  case n of {
   N0 -> x;
   Npos p -> iter p f x}

eq_dec0 :: N -> N -> Sumbool
eq_dec0 n m =
  n_rec (\m0 ->
    case m0 of {
     N0 -> Left;
     Npos p -> Right}) (\p m0 ->
    case m0 of {
     N0 -> Right;
     Npos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0)}) n
    m

discr :: N -> Sumor Prelude.Integer
discr n =
  case n of {
   N0 -> Inright;
   Npos p -> Inleft p}

binary_rect :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rect f0 f2 fS2 n =
  let {f2' = \p -> f2 (Npos p)} in
  let {fS2' = \p -> fS2 (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> positive_rect fS2' f2' (fS2 N0 f0) p}

binary_rec :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rec =
  binary_rect

peano_rect0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rect0 f0 f n =
  let {f' = \p -> f (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> peano_rect (f N0 f0) f' p}

peano_rec0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rec0 =
  peano_rect0

leb_spec1 :: N -> N -> Reflect
leb_spec1 x y =
  iff_reflect (leb0 x y)

ltb_spec1 :: N -> N -> Reflect
ltb_spec1 x y =
  iff_reflect (ltb0 x y)

recursion :: a1 -> (N -> a1 -> a1) -> N -> a1
recursion =
  peano_rect0

sqrt_up :: N -> N
sqrt_up a =
  case compare N0 a of {
   Prelude.LT -> succ (sqrt0 (pred a));
   _ -> N0}

log2_up :: N -> N
log2_up a =
  case compare (Npos 1) a of {
   Prelude.LT -> succ (log2 (pred a));
   _ -> N0}

lcm :: N -> N -> N
lcm a b =
  mul a (div b (gcd0 a b))

eqb_spec0 :: N -> N -> Reflect
eqb_spec0 x y =
  iff_reflect (eqb0 x y)

b2n :: Bool -> N
b2n b =
  case b of {
   True -> Npos 1;
   False -> N0}

setbit :: N -> N -> N
setbit a n =
  lor0 a (shiftl0 (Npos 1) n)

clearbit :: N -> N -> N
clearbit a n =
  ldiff0 a (shiftl0 (Npos 1) n)

ones :: N -> N
ones n =
  pred (shiftl0 (Npos 1) n)

lnot :: N -> N -> N
lnot a n =
  lxor0 a (ones n)

max_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max n m) __ (hl __);
   _ -> compat m (max n m) __ (hr __)}

max_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case1 n m x x0 x1 =
  max_case_strong1 n m x (\_ -> x0) (\_ -> x1)

max_dec1 :: N -> N -> Sumbool
max_dec1 n m =
  max_case1 n m (\x y _ h0 -> h0) Left Right

min_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min n m) __ (hr __);
   _ -> compat n (min n m) __ (hl __)}

min_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case1 n m x x0 x1 =
  min_case_strong1 n m x (\_ -> x0) (\_ -> x1)

min_dec1 :: N -> N -> Sumbool
min_dec1 n m =
  min_case1 n m (\x y _ h0 -> h0) Left Right

max_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
max_case_strong2 n m x x0 =
  max_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case2 :: N -> N -> a1 -> a1 -> a1
max_case2 n m x x0 =
  max_case_strong2 n m (\_ -> x) (\_ -> x0)

max_dec2 :: N -> N -> Sumbool
max_dec2 =
  max_dec1

min_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
min_case_strong2 n m x x0 =
  min_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case2 :: N -> N -> a1 -> a1 -> a1
min_case2 n m x x0 =
  min_case_strong2 n m (\_ -> x) (\_ -> x0)

min_dec2 :: N -> N -> Sumbool
min_dec2 =
  min_dec1

lt_eq_lt_dec :: Nat -> Nat -> Sumor Sumbool
lt_eq_lt_dec n m =
  nat_rec (\m0 ->
    case m0 of {
     O -> Inleft Right;
     S m1 -> Inleft Left}) (\n0 iHn m0 ->
    case m0 of {
     O -> Inright;
     S m1 -> iHn m1}) n m

le_lt_dec :: Nat -> Nat -> Sumbool
le_lt_dec n m =
  nat_rec (\m0 -> Left) (\n0 iHn m0 ->
    case m0 of {
     O -> Right;
     S m1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (iHn m1)}) n m

le_lt_eq_dec :: Nat -> Nat -> Sumbool
le_lt_eq_dec n m =
  let {s = lt_eq_lt_dec n m} in
  case s of {
   Inleft s0 -> s0;
   Inright -> false_rec}

type T1 = Prelude.Integer

zero0 :: Prelude.Integer
zero0 =
  0

one0 :: Prelude.Integer
one0 =
  (\x -> x) 1

two0 :: Prelude.Integer
two0 =
  (\x -> x) ((\x -> 2 Prelude.* x) 1)

double0 :: Prelude.Integer -> Prelude.Integer
double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x)
    p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x)
    p))
    x

succ_double0 :: Prelude.Integer -> Prelude.Integer
succ_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (\x -> x)
    1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    (\p -> Prelude.negate
    (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> Prelude.negate
    1)
    (\p -> (\x -> x)
    (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1)
    p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      double0 (pos_sub p q))
      (\q ->
      succ_double0 (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x)
      p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q ->
      pred_double0 (pos_sub p q))
      (\q ->
      double0 (pos_sub p q))
      (\_ -> (\x -> x)
      (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x)
      q))
      (\q -> Prelude.negate
      (pred_double q))
      (\_ ->
      0)
      y)
    x

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\x0 -> Prelude.negate
    x0)
    (\x0 -> (\x -> x)
    x0)
    x

succ0 :: Prelude.Integer -> Prelude.Integer
succ0 x =
  (Prelude.+) x ((\x -> x) 1)

pred0 :: Prelude.Integer -> Prelude.Integer
pred0 x =
  (Prelude.+) x (Prelude.negate 1)

pow_pos :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow_pos z n =
  iter n ((Prelude.*) z) ((\x -> x) 1)

pow1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow1 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (\x -> x)
    1)
    (\p ->
    pow_pos x p)
    (\p ->
    0)
    y

square1 :: Prelude.Integer -> Prelude.Integer
square1 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    (square p))
    (\p -> (\x -> x)
    (square p))
    x

compare0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Ordering
compare0 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.EQ)
      (\y' ->
      Prelude.LT)
      (\y' ->
      Prelude.GT)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.GT)
      (\y' ->
      (Prelude.compare) x' y')
      (\y' ->
      Prelude.GT)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Prelude.LT)
      (\y' ->
      Prelude.LT)
      (\y' ->
      compOpp ((Prelude.compare) x' y'))
      y)
    x

sgn :: Prelude.Integer -> Prelude.Integer
sgn z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    1)
    (\p -> Prelude.negate
    1)
    z

leb1 :: Prelude.Integer -> Prelude.Integer -> Bool
leb1 x y =
  case compare0 x y of {
   Prelude.GT -> False;
   _ -> True}

ltb1 :: Prelude.Integer -> Prelude.Integer -> Bool
ltb1 x y =
  case compare0 x y of {
   Prelude.LT -> True;
   _ -> False}

geb :: Prelude.Integer -> Prelude.Integer -> Bool
geb x y =
  case compare0 x y of {
   Prelude.LT -> False;
   _ -> True}

gtb :: Prelude.Integer -> Prelude.Integer -> Bool
gtb x y =
  case compare0 x y of {
   Prelude.GT -> True;
   _ -> False}

eqb1 :: Prelude.Integer -> Prelude.Integer -> Bool
eqb1 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      True)
      (\p ->
      False)
      (\p ->
      False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      False)
      (\q ->
      eqb p q)
      (\p0 ->
      False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      False)
      (\p0 ->
      False)
      (\q ->
      eqb p q)
      y)
    x

abs :: Prelude.Integer -> Prelude.Integer
abs z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    p)
    (\p -> (\x -> x)
    p)
    z

abs_nat :: Prelude.Integer -> Nat
abs_nat z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    O)
    (\p ->
    to_nat p)
    (\p ->
    to_nat p)
    z

abs_N :: Prelude.Integer -> N
abs_N z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    N0)
    (\p -> Npos
    p)
    (\p -> Npos
    p)
    z

to_nat1 :: Prelude.Integer -> Nat
to_nat1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    O)
    (\p ->
    to_nat p)
    (\p ->
    O)
    z

to_N :: Prelude.Integer -> N
to_N z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    N0)
    (\p -> Npos
    p)
    (\p ->
    N0)
    z

of_nat1 :: Nat -> Prelude.Integer
of_nat1 n =
  case n of {
   O -> 0;
   S n0 -> (\x -> x) (of_succ_nat n0)}

of_N :: N -> Prelude.Integer
of_N n =
  case n of {
   N0 -> 0;
   Npos p -> (\x -> x) p}

to_pos :: Prelude.Integer -> Prelude.Integer
to_pos z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    1)
    (\p ->
    p)
    (\p ->
    1)
    z

iter1 :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter1 n f x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    x)
    (\p ->
    iter p f x)
    (\p ->
    x)
    n

pos_div_eucl0 :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
                 Prelude.Integer
pos_div_eucl0 a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {
       r' = (Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb1 r' b of {
       True -> Pair ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       False -> Pair
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r} in
      case ltb1 r' b of {
       True -> Pair ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       False -> Pair
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\_ ->
    case leb1 ((\x -> x) ((\x -> 2 Prelude.* x) 1)) b of {
     True -> Pair 0 ((\x -> x) 1);
     False -> Pair ((\x -> x) 1) 0})
    a

div_eucl0 :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
             Prelude.Integer
div_eucl0 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> Pair 0
    0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Pair 0
      0)
      (\p ->
      pos_div_eucl0 a' b)
      (\b' ->
      case pos_div_eucl0 a' ((\x -> x) b') of {
       Pair q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
          (\_ -> Pair (opp q)
          0)
          (\p -> Pair (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          (\p -> Pair (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Pair 0
      0)
      (\p ->
      case pos_div_eucl0 a' b of {
       Pair q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
          (\_ -> Pair (opp q)
          0)
          (\p0 -> Pair (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          (\p0 -> Pair (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          r})
      (\b' ->
      case pos_div_eucl0 a' ((\x -> x) b') of {
       Pair q r -> Pair q (opp r)})
      b)
    a

div1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div1 = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

modulo0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo0 = (\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)

quotrem :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
           Prelude.Integer
quotrem a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> Pair 0
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Pair 0
      a)
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (of_N r)})
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (of_N r)})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Pair 0
      a)
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (opp (of_N r))})
      (\b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (opp (of_N r))})
      b)
    a

quot :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
quot a b =
  fst (quotrem a b)

rem :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
rem a b =
  snd (quotrem a b)

even0 :: Prelude.Integer -> Bool
even0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    True)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      False)
      (\p0 ->
      True)
      (\_ ->
      False)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      False)
      (\p0 ->
      True)
      (\_ ->
      False)
      p)
    z

odd0 :: Prelude.Integer -> Bool
odd0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    False)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      True)
      (\p0 ->
      False)
      (\_ ->
      True)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 ->
      True)
      (\p0 ->
      False)
      (\_ ->
      True)
      p)
    z

div3 :: Prelude.Integer -> Prelude.Integer
div3 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> (\x -> x)
      (div2 p))
      (\p0 -> (\x -> x)
      (div2 p))
      (\_ ->
      0)
      p)
    (\p -> Prelude.negate
    (div2_up p))
    z

quot2 :: Prelude.Integer -> Prelude.Integer
quot2 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> (\x -> x)
      (div2 p))
      (\p0 -> (\x -> x)
      (div2 p))
      (\_ ->
      0)
      p)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p0 -> Prelude.negate
      (div2 p))
      (\p0 -> Prelude.negate
      (div2 p))
      (\_ ->
      0)
      p)
    z

log0 :: Prelude.Integer -> Prelude.Integer
log0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else if Prelude.odd n then fI (n `Prelude.div` 2) else fO (n `Prelude.div` 2))
      (\p -> (\x -> x)
      (size p))
      (\p -> (\x -> x)
      (size p))
      (\_ ->
      0)
      p0)
    (\p ->
    0)
    z

sqrtrem1 :: Prelude.Integer -> Prod Prelude.Integer Prelude.Integer
sqrtrem1 n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> Pair 0
    0)
    (\p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair ((\x -> x) s) ((\x -> x) r);
       _ -> Pair ((\x -> x) s) 0}})
    (\p -> Pair 0
    0)
    n

sqrt1 :: Prelude.Integer -> Prelude.Integer
sqrt1 n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\p -> (\x -> x)
    (sqrt p))
    (\p ->
    0)
    n

gcd1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    abs b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      abs a)
      (\b0 -> (\x -> x)
      (gcd a0 b0))
      (\b0 -> (\x -> x)
      (gcd a0 b0))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      abs a)
      (\b0 -> (\x -> x)
      (gcd a0 b0))
      (\b0 -> (\x -> x)
      (gcd a0 b0))
      b)
    a

ggcd1 :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
         (Prod Prelude.Integer Prelude.Integer)
ggcd1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> Pair (abs b) (Pair 0
    (sgn b)))
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Pair (abs a) (Pair (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair ((\x -> x) g) (Pair ((\x -> x) aa) ((\x -> x)
          bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair ((\x -> x) g) (Pair ((\x -> x) aa)
          (Prelude.negate bb))}})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Pair (abs a) (Pair (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair ((\x -> x) g) (Pair (Prelude.negate aa)
          ((\x -> x) bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair ((\x -> x) g) (Pair (Prelude.negate aa)
          (Prelude.negate bb))}})
      b)
    a

testbit1 :: Prelude.Integer -> Prelude.Integer -> Bool
testbit1 a n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    odd0 a)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      False)
      (\a0 ->
      testbit a0 (Npos p))
      (\a0 ->
      negb (testbit0 (pred_N a0) (Npos p)))
      a)
    (\p ->
    False)
    n

shiftl1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftl1 a n =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    a)
    (\p ->
    iter p ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1))) a)
    (\p ->
    iter p div3 a)
    n

shiftr1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftr1 a n =
  shiftl1 a (opp n)

lor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> (\x -> x)
      (lor a0 b0))
      (\b0 -> Prelude.negate
      (succ_pos (ldiff0 (pred_N b0) (Npos a0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (ldiff0 (pred_N a0) (Npos b0))))
      (\b0 -> Prelude.negate
      (succ_pos (land0 (pred_N a0) (pred_N b0))))
      b)
    a

land1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
land1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      0)
      (\b0 ->
      of_N (land a0 b0))
      (\b0 ->
      of_N (ldiff0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      0)
      (\b0 ->
      of_N (ldiff0 (Npos b0) (pred_N a0)))
      (\b0 -> Prelude.negate
      (succ_pos (lor0 (pred_N a0) (pred_N b0))))
      b)
    a

ldiff1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ldiff1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    0)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 ->
      of_N (ldiff a0 b0))
      (\b0 ->
      of_N (land0 (Npos a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (lor0 (pred_N a0) (Npos b0))))
      (\b0 ->
      of_N (ldiff0 (pred_N b0) (pred_N a0)))
      b)
    a

lxor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lxor1 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 ->
      of_N (lxor a0 b0))
      (\b0 -> Prelude.negate
      (succ_pos (lxor0 (Npos a0) (pred_N b0))))
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      a)
      (\b0 -> Prelude.negate
      (succ_pos (lxor0 (pred_N a0) (Npos b0))))
      (\b0 ->
      of_N (lxor0 (pred_N a0) (pred_N b0)))
      b)
    a

eq_dec1 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec1 x y =
  z_rec (\y0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Left)
      (\p ->
      Right)
      (\p ->
      Right)
      y0) (\p y0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Right)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0))
      (\p0 ->
      Right)
      y0) (\p y0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ ->
      Right)
      (\p0 ->
      Right)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0))
      y0) x y

leb_spec2 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec2 x y =
  iff_reflect (leb1 x y)

ltb_spec2 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec2 x y =
  iff_reflect (ltb1 x y)

sqrt_up0 :: Prelude.Integer -> Prelude.Integer
sqrt_up0 a =
  case compare0 0 a of {
   Prelude.LT -> succ0 (sqrt1 (pred0 a));
   _ -> 0}

log2_up0 :: Prelude.Integer -> Prelude.Integer
log2_up0 a =
  case compare0 ((\x -> x) 1) a of {
   Prelude.LT -> succ0 (log0 (pred0 a));
   _ -> 0}

div4 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div4 =
  quot

modulo1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo1 =
  rem

lcm0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lcm0 a b =
  abs ((Prelude.*) a (div1 b (gcd1 a b)))

eqb_spec1 :: Prelude.Integer -> Prelude.Integer -> Reflect
eqb_spec1 x y =
  iff_reflect (eqb1 x y)

b2z :: Bool -> Prelude.Integer
b2z b =
  case b of {
   True -> (\x -> x) 1;
   False -> 0}

setbit0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
setbit0 a n =
  lor1 a (shiftl1 ((\x -> x) 1) n)

clearbit0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
clearbit0 a n =
  ldiff1 a (shiftl1 ((\x -> x) 1) n)

lnot0 :: Prelude.Integer -> Prelude.Integer
lnot0 a =
  pred0 (opp a)

ones0 :: Prelude.Integer -> Prelude.Integer
ones0 n =
  pred0 (shiftl1 ((\x -> x) 1) n)

max_case_strong3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                    Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat n (Prelude.max n m) __ (hl __);
   _ -> compat m (Prelude.max n m) __ (hr __)}

max_case3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
             Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case3 n m x x0 x1 =
  max_case_strong3 n m x (\_ -> x0) (\_ -> x1)

max_dec3 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec3 n m =
  max_case3 n m (\x y _ h0 -> h0) Left Right

min_case_strong3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                    Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat m (Prelude.min n m) __ (hr __);
   _ -> compat n (Prelude.min n m) __ (hl __)}

min_case3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
             Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case3 n m x x0 x1 =
  min_case_strong3 n m x (\_ -> x0) (\_ -> x1)

min_dec3 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec3 n m =
  min_case3 n m (\x y _ h0 -> h0) Left Right

max_case_strong4 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong4 n m x x0 =
  max_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case4 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
max_case4 n m x x0 =
  max_case_strong4 n m (\_ -> x) (\_ -> x0)

max_dec4 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec4 =
  max_dec3

min_case_strong4 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong4 n m x x0 =
  min_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case4 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
min_case4 n m x x0 =
  min_case_strong4 n m (\_ -> x) (\_ -> x0)

min_dec4 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec4 =
  min_dec3

z_lt_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_lt_dec x y =
  case compare0 x y of {
   Prelude.LT -> Left;
   _ -> Right}

z_lt_ge_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_lt_ge_dec x y =
  z_lt_dec x y

z_lt_le_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_lt_le_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_lt_ge_dec x y)

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 l0 iHl ->
    let {s = h a0 a} in
    case s of {
     Left -> Left;
     Right -> iHl}) l

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

qnum :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer
qnum q =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\qnum0 qden0 ->
    qnum0)
    q

qden :: (Data.Ratio.Ratio Prelude.Integer) -> Prelude.Integer
qden q =
  (\fp qn -> fp (Data.Ratio.numerator qn) (Data.Ratio.denominator qn))
    (\qnum0 qden0 ->
    qden0)
    q

qplus :: (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer)
qplus x y =
  (\x y -> (Data.Ratio.%) x y)
    ((Prelude.+) ((Prelude.*) (qnum x) ((\x -> x) (qden y)))
      ((Prelude.*) (qnum y) ((\x -> x) (qden x))))
    ((Prelude.*) (qden x) (qden y))

qmult :: (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer) ->
         (Data.Ratio.Ratio Prelude.Integer)
qmult x y =
  (\x y -> (Data.Ratio.%) x y) ((Prelude.*) (qnum x) (qnum y))
    ((Prelude.*) (qden x) (qden y))

qopp :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qopp x =
  (\x y -> (Data.Ratio.%) x y) (opp (qnum x)) (qden x)

qminus :: (Data.Ratio.Ratio Prelude.Integer) ->
          (Data.Ratio.Ratio Prelude.Integer) ->
          (Data.Ratio.Ratio Prelude.Integer)
qminus x y =
  qplus x (qopp y)

qinv :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qinv x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (\x y -> (Data.Ratio.%) x y) 0
    1)
    (\p -> (\x y -> (Data.Ratio.%) x y) ((\x -> x) (qden x))
    p)
    (\p -> (\x y -> (Data.Ratio.%) x y) (Prelude.negate (qden x))
    p)
    (qnum x)

qdiv :: (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer) ->
        (Data.Ratio.Ratio Prelude.Integer)
qdiv x y =
  qmult x (qinv y)

qlt_le_dec :: (Data.Ratio.Ratio Prelude.Integer) ->
              (Data.Ratio.Ratio Prelude.Integer) -> Sumbool
qlt_le_dec x y =
  z_lt_le_dec ((Prelude.*) (qnum x) ((\x -> x) (qden y)))
    ((Prelude.*) (qnum y) ((\x -> x) (qden x)))

mk_nfj :: a1 -> a1
mk_nfj j =
  j

type Rule judgement = ()

type App judgement =
  judgement -> () -> SigT (Rule judgement) (SigT judgement ())

data Pf judgement =
   Ax judgement
 | Mkp judgement judgement (Pf judgement)

extend :: (a1 -> a2) -> (List (Rule a1)) -> (App a1) -> a1 -> a1 -> (Pf 
          a1) -> SigT a1 (Prod (Pf a1) ())
extend m rules happ a b pab =
  let {happ0 = happ b} in
  case happ0 __ of {
   ExistT _ happ1 ->
    case happ1 of {
     ExistT c _ -> ExistT c (Pair (Mkp c b pab) __)}}

termination_aux :: (a1 -> Sum () ()) -> (a1 -> a2) -> (List (Rule a1)) ->
                   (App a1) -> a2 -> a1 -> a1 -> (Pf a1) -> SigT a1
                   (Prod () (Pf a1))
termination_aux final_dec0 m rules happ n a b x =
  well_founded_induction_type (\w iH a0 b0 _ _ hab ->
    let {hex = extend m rules happ a0 b0 hab} in
    case hex of {
     ExistT c p ->
      case p of {
       Pair hex1 _ ->
        let {s = final_dec0 c} in
        case s of {
         Inl _ -> ExistT c (Pair __ hex1);
         Inr _ ->
          eq_rect_r w iH (m (mk_nfj b0)) (m (mk_nfj c)) __ a0 c __ __ hex1}}})
    n a b __ __ x

termination :: (a1 -> Sum () ()) -> (a1 -> a2) -> (List (Rule a1)) -> (App
               a1) -> a1 -> SigT a1 (Prod () (Pf a1))
termination final_dec0 m rules happ a =
  let {s = final_dec0 a} in
  case s of {
   Inl _ -> ExistT a (Pair __ (Ax a));
   Inr _ -> termination_aux final_dec0 m rules happ (m (mk_nfj a)) a a (Ax a)}

type Ballot cand = Prod (List cand) (Data.Ratio.Ratio Prelude.Integer)

data FT_Judgement cand =
   State (Prod
         (Prod
         (Prod
         (Prod
         (Prod (List (Ballot cand))
         (cand -> (Data.Ratio.Ratio Prelude.Integer)))
         (cand -> List (Ballot cand))) (List cand)) (List cand)) (List cand))
 | Winners (List cand)

final_dec :: (List a1) -> Nat -> (FT_Judgement a1) -> Sum () ()
final_dec cand_all0 st0 j =
  case j of {
   State p -> Inr __;
   Winners l -> Inl __}

type FT_Rule cand = ()

removel :: (a1 -> (List a1) -> Sumbool) -> (List a1) -> (List a1) -> List a1
removel cand_in_dec k l =
  case l of {
   Nil -> Nil;
   Cons l0 ls ->
    case cand_in_dec l0 k of {
     Left -> removel cand_in_dec k ls;
     Right -> Cons l0 (removel cand_in_dec k ls)}}

sum :: (List a1) -> (List (Ballot a1)) -> (Data.Ratio.Ratio Prelude.Integer)
sum cand_all0 l =
  case l of {
   Nil -> (\x y -> (Data.Ratio.%) x y) 0 1;
   Cons l0 ls -> qplus (snd l0) (sum cand_all0 ls)}

fTR :: (List a1) -> (a1 -> (List a1) -> Sumbool) -> Nat ->
       (Data.Ratio.Ratio Prelude.Integer) -> List (FT_Rule a1)
fTR cand_all0 cand_in_dec st0 qu0 =
  Cons __ (Cons __ (Cons __ (Cons __ (Cons __ (Cons __ Nil)))))

type FT_WFO = Prod Nat (Prod Nat Nat)

fT_m :: (List a1) -> Nat -> (FT_Judgement a1) -> FT_WFO
fT_m cand_all0 st0 h =
  case h of {
   State p ->
    case p of {
     Pair p0 x ->
      case p0 of {
       Pair p1 x0 ->
        case p1 of {
         Pair p2 x1 ->
          case p2 of {
           Pair p3 x2 ->
            case p3 of {
             Pair ba t -> Pair (length (proj1_sig x)) (Pair (length x1)
              (length ba))}}}}};
   Winners l -> false_rec}

list_min :: (List a1) -> (a1 -> (Data.Ratio.Ratio Prelude.Integer)) -> Sum 
            () (SigT a1 ())
list_min l f =
  list_rect (Inl __) (\l0 ls iHls ->
    case iHls of {
     Inl _ -> Inr (ExistT l0 __);
     Inr s -> Inr
      (case s of {
        ExistT x _ ->
         let {h1 = qlt_le_dec (f x) (f l0)} in
         let {h2 = sumbool_rec (\_ -> Left) (\_ -> Right) h1} in
         case h2 of {
          Left -> ExistT x __;
          Right -> ExistT l0 __}})}) l

remc :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> List a1
remc cand_eq_dec c l =
  case l of {
   Nil -> Nil;
   Cons l0 ls ->
    case cand_eq_dec c l0 of {
     Left -> ls;
     Right -> Cons l0 (remc cand_eq_dec c ls)}}

update_pile :: (List a1) -> (a1 -> (List a1) -> Sumbool) ->
               (Data.Ratio.Ratio Prelude.Integer) -> (a1 -> List (Ballot a1))
               -> (a1 -> (Data.Ratio.Ratio Prelude.Integer)) -> (List 
               a1) -> a1 -> List (Ballot a1)
update_pile cand_all0 cand_in_dec qu0 p t l c =
  case cand_in_dec c l of {
   Left ->
    map (\b -> Pair (fst b) (qmult (snd b) (qdiv (qminus (t c) qu0) (t c))))
      (p c);
   Right -> p c}

emp :: (List a1) -> (a1 -> a1 -> Sumbool) -> a1 -> (a1 -> List (Ballot a1))
       -> a1 -> List (Ballot a1)
emp cand_all0 cand_eq_dec c p d =
  case cand_eq_dec c d of {
   Left -> Nil;
   Right -> p d}

extend_ordered_type :: (a1 -> (Data.Ratio.Ratio Prelude.Integer)) -> (List
                       a1) -> a1 -> SigT (List a1) (SigT (List a1) ())
extend_ordered_type f x a =
  list_rect (\_ -> ExistT Nil (ExistT Nil __)) (\a0 x0 iHx _ ->
    case iHx __ of {
     ExistT x1 s ->
      case s of {
       ExistT z _ ->
        let {hyp = qlt_le_dec (f a0) (f a)} in
        case hyp of {
         Left ->
          case x1 of {
           Nil -> ExistT Nil (ExistT (Cons a0 z) __);
           Cons a1 x2 -> false_rect};
         Right -> ExistT (Cons a0 x1) (ExistT z __)}}}) x __

list_max :: (List a1) -> (a1 -> (Data.Ratio.Ratio Prelude.Integer)) -> Sum 
            () (SigT a1 ())
list_max l f =
  list_rect (Inl __) (\a l0 iHl ->
    case iHl of {
     Inl _ -> Inr (eq_rect_r Nil (ExistT a __) l0);
     Inr s -> Inr
      (case s of {
        ExistT x _ ->
         let {h1 = qlt_le_dec (f a) (f x)} in
         case h1 of {
          Left -> ExistT x __;
          Right -> ExistT a __}})}) l

list_max_cor :: (List a1) -> (a1 -> (Data.Ratio.Ratio Prelude.Integer)) ->
                SigT a1 ()
list_max_cor l f =
  let {h0 = list_max l f} in
  case h0 of {
   Inl _ -> false_rect;
   Inr s -> s}

constructing_electable_first :: (a1 -> a1 -> Sumbool) -> (a1 -> (List 
                                a1) -> Sumbool) -> Nat ->
                                (Data.Ratio.Ratio Prelude.Integer) ->
                                (List a1) -> (a1 ->
                                (Data.Ratio.Ratio Prelude.Integer)) ->
                                (List a1) -> SigT (List a1) ()
constructing_electable_first cand_eq_dec cand_in_dec st0 qu0 e f h =
  let {l = proj1_sig h} in
  list_rect (\_ -> ExistT Nil __) (\a l0 iHl _ ->
    let {hyp1 = qlt_le_dec (f a) qu0} in
    case hyp1 of {
     Left ->
      let {iHl0 = iHl __} in
      case iHl0 of {
       ExistT m _ ->
        let {s = cand_in_dec a m} in
        case s of {
         Left -> false_rect;
         Right -> ExistT m __}};
     Right ->
      let {iHl0 = iHl __} in
      case iHl0 of {
       ExistT m _ ->
        let {s = cand_in_dec a m} in
        case s of {
         Left -> false_rect;
         Right ->
          let {
           h0 = le_lt_eq_dec (length m) (minus st0 (length (proj1_sig e)))}
          in
          case h0 of {
           Left ->
            let {h1 = extend_ordered_type f m a} in
            case h1 of {
             ExistT m1 s0 ->
              case s0 of {
               ExistT m2 _ -> ExistT (app m1 (app (Cons a Nil) m2)) __}};
           Right -> ExistT m __}}}}) l __

is_first_hopeful :: (a1 -> a1 -> Sumbool) -> (a1 -> (List a1) -> Sumbool) ->
                    a1 -> (List a1) -> (List a1) -> Bool
is_first_hopeful cand_eq_dec cand_in_dec c h l =
  case l of {
   Nil -> False;
   Cons l0 ls ->
    case cand_eq_dec l0 c of {
     Left -> True;
     Right ->
      case cand_in_dec l0 h of {
       Left -> False;
       Right -> is_first_hopeful cand_eq_dec cand_in_dec c h ls}}}

list_is_first_hopeful :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> (List
                         a1) -> Sumbool) -> a1 -> (List a1) -> (List
                         (Ballot a1)) -> List (Ballot a1)
list_is_first_hopeful cand_all0 cand_eq_dec cand_in_dec c h ba =
  case ba of {
   Nil -> Nil;
   Cons b0 bas ->
    case is_first_hopeful cand_eq_dec cand_in_dec c h (proj1_sig (fst b0)) of {
     True -> Cons b0
      (list_is_first_hopeful cand_all0 cand_eq_dec cand_in_dec c h bas);
     False -> list_is_first_hopeful cand_all0 cand_eq_dec cand_in_dec c h bas}}

app_FT :: (List a1) -> (a1 -> a1 -> Sumbool) -> (a1 -> (List a1) -> Sumbool)
          -> Nat -> (Data.Ratio.Ratio Prelude.Integer) -> (FT_Judgement 
          a1) -> SigT (Rule (FT_Judgement a1)) (SigT (FT_Judgement a1) ())
app_FT cand_all0 cand_eq_dec cand_in_dec st0 qu0 p =
  case p of {
   State p0 ->
    case p0 of {
     Pair p1 x ->
      case p1 of {
       Pair p2 x0 ->
        case p2 of {
         Pair p3 x1 ->
          case p3 of {
           Pair p4 x2 ->
            case p4 of {
             Pair ba t ->
              case ba of {
               Nil ->
                let {
                 s = le_lt_dec
                       (plus (length (proj1_sig x0)) (length (proj1_sig x)))
                       st0}
                in
                case s of {
                 Left -> ExistT __ (ExistT (Winners
                  (app (proj1_sig x0) (proj1_sig x))) __);
                 Right ->
                  let {x3 = \_ -> list_max_cor (proj1_sig x) t} in
                  let {
                   x4 = let {l = proj1_sig x} in
                        list_rect (\_ x4 -> Inl __) (\a l0 iHl _ x4 ->
                          let {x5 = x4 __} in
                          case x5 of {
                           ExistT x6 _ ->
                            let {h2 = qlt_le_dec (t x6) qu0} in
                            case h2 of {
                             Left -> Inl __;
                             Right -> Inr (ExistT x6 __)}}) l __ x3}
                  in
                  case x4 of {
                   Inl _ ->
                    case x1 of {
                     Nil ->
                      let {h2 = list_min (proj1_sig x) t} in
                      case h2 of {
                       Inl _ -> Prelude.error "absurd case";
                       Inr s0 ->
                        case s0 of {
                         ExistT x5 _ -> ExistT __ (ExistT (State (Pair (Pair
                          (Pair (Pair (Pair (x2 x5) t)
                          (emp cand_all0 cand_eq_dec x5 x2)) Nil) x0)
                          (remc cand_eq_dec x5 (proj1_sig x)))) __)}};
                     Cons c bl -> ExistT __ (ExistT (State (Pair (Pair (Pair
                      (Pair (Pair (x2 c) t) (emp cand_all0 cand_eq_dec c x2))
                      bl) x0) x)) __)};
                   Inr s0 ->
                    let {hypo_2 = le_lt_dec st0 (length (proj1_sig x0))} in
                    case hypo_2 of {
                     Left ->
                      let {h = le_lt_eq_dec st0 (length (proj1_sig x0))} in
                      case h of {
                       Left -> false_rect;
                       Right -> ExistT __ (ExistT (Winners (proj1_sig x0))
                        __)};
                     Right ->
                      let {
                       h = constructing_electable_first cand_eq_dec
                             cand_in_dec st0 qu0 x0 t x}
                      in
                      case h of {
                       ExistT l _ -> ExistT __ (ExistT (State (Pair (Pair
                        (Pair (Pair (Pair Nil t)
                        (update_pile cand_all0 cand_in_dec qu0 x2 t l))
                        (app x1 l)) (app (proj1_sig x0) l))
                        (removel cand_in_dec l (proj1_sig x)))) __)}}}};
               Cons b ba0 -> ExistT __ (ExistT (State (Pair (Pair (Pair (Pair
                (Pair Nil (\c ->
                case cand_in_dec c (proj1_sig x) of {
                 Left ->
                  sum cand_all0
                    (app (x2 c)
                      (list_is_first_hopeful cand_all0 cand_eq_dec
                        cand_in_dec c (proj1_sig x) (Cons b ba0)));
                 Right -> t c})) (\c ->
                case cand_in_dec c (proj1_sig x) of {
                 Left ->
                  app (x2 c)
                    (list_is_first_hopeful cand_all0 cand_eq_dec cand_in_dec
                      c (proj1_sig x) (Cons b ba0));
                 Right -> x2 c})) x1) x0) x)) __)}}}}}};
   Winners l -> false_rect}

data Cand =
   A
 | B
 | C

cand_all :: List Cand
cand_all =
  Cons A (Cons B (Cons C Nil))

st :: Nat
st =
  S (S O)

qu :: (Data.Ratio.Ratio Prelude.Integer)
qu =
  (\x y -> (Data.Ratio.%) x y) ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1)))))))))))))) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1))))))))))))

canddec :: Cand -> Cand -> Sumbool
canddec c d =
  case c of {
   A ->
    case d of {
     A -> Left;
     _ -> Right};
   B ->
    case d of {
     B -> Left;
     _ -> Right};
   C ->
    case d of {
     C -> Left;
     _ -> Right}}

listdec :: Cand -> (List Cand) -> Sumbool
listdec c l =
  in_dec canddec c l

hunion_count :: (FT_Judgement Cand) -> SigT (FT_Judgement Cand)
                (Prod () (Pf (FT_Judgement Cand)))
hunion_count =
  termination (final_dec cand_all st) (fT_m cand_all st)
    (fTR cand_all listdec st qu) (\x _ ->
    app_FT cand_all canddec listdec st qu x)

