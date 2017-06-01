module Lib where

import qualified Prelude
import System.Random
__ :: any
__ = Prelude.error "Logical or arity value used"

"see if changes applied"
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

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
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

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Bool -> Reflect
iff_reflect b =
  case b of {
   True -> and_rec (\_ _ -> ReflectT);
   False -> and_rec (\_ _ -> ReflectF)}

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

data Positive =
   XI Positive
 | XO Positive
 | XH

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p0 -> f p0 (positive_rect f f0 f1 p0);
   XO p0 -> f0 p0 (positive_rect f f0 f1 p0);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Positive

n_rect :: a1 -> (Positive -> a1) -> N -> a1
n_rect f f0 n =
  case n of {
   N0 -> f;
   Npos x -> f0 x}

n_rec :: a1 -> (Positive -> a1) -> N -> a1
n_rec =
  n_rect

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

z_rect :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rect f f0 f1 z =
  case z of {
   Z0 -> f;
   Zpos x -> f0 x;
   Zneg x -> f1 x}

z_rec :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rec =
  z_rect

type T = Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH ->
    case y of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH ->
    case y of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

pred :: Positive -> Positive
pred x =
  case x of {
   XI p -> XO p;
   XO p -> pred_double p;
   XH -> XH}

pred_N :: Positive -> N
pred_N x =
  case x of {
   XI p -> Npos (XO p);
   XO p -> Npos (pred_double p);
   XH -> N0}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

mask_rect :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos x -> f0 x;
   IsNeg -> f1}

mask_rec :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q ->
    case q of {
     XH -> IsNul;
     _ -> IsPos (pred q)};
   _ -> IsNeg}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH ->
    case y of {
     XH -> IsNul;
     _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter :: Positive -> (a1 -> a1) -> a1 -> a1
iter n f x =
  case n of {
   XI n' -> f (iter n' f (iter n' f x));
   XO n' -> iter n' f (iter n' f x);
   XH -> f x}

pow :: Positive -> Positive -> Positive
pow x y =
  iter y (mul x) XH

square :: Positive -> Positive
square p =
  case p of {
   XI p0 -> XI (XO (add (square p0) p0));
   XO p0 -> XO (XO (square p0));
   XH -> XH}

div2 :: Positive -> Positive
div2 p =
  case p of {
   XI p0 -> p0;
   XO p0 -> p0;
   XH -> XH}

div2_up :: Positive -> Positive
div2_up p =
  case p of {
   XI p0 -> succ p0;
   XO p0 -> p0;
   XH -> XH}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

size :: Positive -> Positive
size p =
  case p of {
   XI p0 -> succ (size p0);
   XO p0 -> succ (size p0);
   XH -> XH}

compare_cont :: Positive -> Positive -> Comparison -> Comparison
compare_cont x y r =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont p q r;
     XO q -> compare_cont p q Gt;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont p q Lt;
     XO q -> compare_cont p q r;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare x y =
  compare_cont x y Eq

min :: Positive -> Positive -> Positive
min p p' =
  case compare p p' of {
   Gt -> p';
   _ -> p}

max :: Positive -> Positive -> Positive
max p p' =
  case compare p p' of {
   Gt -> p;
   _ -> p'}

eqb :: Positive -> Positive -> Bool
eqb p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> eqb p0 q0;
     _ -> False};
   XO p0 ->
    case q of {
     XO q0 -> eqb p0 q0;
     _ -> False};
   XH ->
    case q of {
     XH -> True;
     _ -> False}}

leb :: Positive -> Positive -> Bool
leb x y =
  case compare x y of {
   Gt -> False;
   _ -> True}

ltb :: Positive -> Positive -> Bool
ltb x y =
  case compare x y of {
   Lt -> True;
   _ -> False}

sqrtrem_step :: (Positive -> Positive) -> (Positive -> Positive) -> (Prod
                Positive Mask) -> Prod Positive Mask
sqrtrem_step f g p =
  case p of {
   Pair s y ->
    case y of {
     IsPos r ->
      let {s' = XI (XO s)} in
      let {r' = g (f r)} in
      case leb s' r' of {
       True -> Pair (XI s) (sub_mask r' s');
       False -> Pair (XO s) (IsPos r')};
     _ -> Pair (XO s) (sub_mask (g (f XH)) (XO (XO XH)))}}

sqrtrem :: Positive -> Prod Positive Mask
sqrtrem p =
  case p of {
   XI p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XI x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XI x) (sqrtrem p1);
     XH -> Pair XH (IsPos (XO XH))};
   XO p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XO x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XO x) (sqrtrem p1);
     XH -> Pair XH (IsPos XH)};
   XH -> Pair XH IsNul}

sqrt :: Positive -> Positive
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Positive -> Positive -> Positive
gcdn n a b =
  case n of {
   O -> XH;
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> a;
         Lt -> gcdn n0 (sub b' a') a;
         Gt -> gcdn n0 (sub a' b') b};
       XO b0 -> gcdn n0 a b0;
       XH -> XH};
     XO a0 ->
      case b of {
       XI p -> gcdn n0 a0 b;
       XO b0 -> XO (gcdn n0 a0 b0);
       XH -> XH};
     XH -> XH}}

gcd :: Positive -> Positive -> Positive
gcd a b =
  gcdn (plus (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Positive -> Positive -> Prod Positive
         (Prod Positive Positive)
ggcdn n a b =
  case n of {
   O -> Pair XH (Pair a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> Pair a (Pair XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           Pair g p ->
            case p of {
             Pair ba aa -> Pair g (Pair aa (add aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           Pair g p ->
            case p of {
             Pair ab bb -> Pair g (Pair (add bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair aa (XO bb))}};
       XH -> Pair XH (Pair a XH)};
     XO a0 ->
      case b of {
       XI p ->
        case ggcdn n0 a0 b of {
         Pair g p0 ->
          case p0 of {
           Pair aa bb -> Pair g (Pair (XO aa) bb)}};
       XO b0 ->
        case ggcdn n0 a0 b0 of {
         Pair g p -> Pair (XO g) p};
       XH -> Pair XH (Pair a XH)};
     XH -> Pair XH (Pair XH b)}}

ggcd :: Positive -> Positive -> Prod Positive (Prod Positive Positive)
ggcd a b =
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

lor :: Positive -> Positive -> Positive
lor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XI (lor p0 q0);
     XH -> p};
   XO p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XO (lor p0 q0);
     XH -> XI p0};
   XH ->
    case q of {
     XO q0 -> XI q0;
     _ -> q}}

land :: Positive -> Positive -> N
land p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> nsucc_double (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> Npos XH};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> N0};
   XH ->
    case q of {
     XO q0 -> N0;
     _ -> Npos XH}}

ldiff :: Positive -> Positive -> N
ldiff p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> nsucc_double (ldiff p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> ndouble (ldiff p0 q0);
     XH -> Npos p};
   XH ->
    case q of {
     XO q0 -> Npos XH;
     _ -> N0}}

lxor :: Positive -> Positive -> N
lxor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (lxor p0 q0);
     XO q0 -> nsucc_double (lxor p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> nsucc_double (lxor p0 q0);
     XO q0 -> ndouble (lxor p0 q0);
     XH -> Npos (XI p0)};
   XH ->
    case q of {
     XI q0 -> Npos (XO q0);
     XO q0 -> Npos (XI q0);
     XH -> N0}}

shiftl_nat :: Positive -> Nat -> Positive
shiftl_nat p n =
  nat_iter n (\x -> XO x) p

shiftr_nat :: Positive -> Nat -> Positive
shiftr_nat p n =
  nat_iter n div2 p

shiftl :: Positive -> N -> Positive
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 (\x -> XO x) p}

shiftr :: Positive -> N -> Positive
shiftr p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 div2 p}

testbit_nat :: Positive -> Nat -> Bool
testbit_nat p n =
  case p of {
   XI p0 ->
    case n of {
     O -> True;
     S n' -> testbit_nat p0 n'};
   XO p0 ->
    case n of {
     O -> False;
     S n' -> testbit_nat p0 n'};
   XH ->
    case n of {
     O -> True;
     S n0 -> False}}

testbit :: Positive -> N -> Bool
testbit p n =
  case p of {
   XI p0 ->
    case n of {
     N0 -> True;
     Npos n0 -> testbit p0 (pred_N n0)};
   XO p0 ->
    case n of {
     N0 -> False;
     Npos n0 -> testbit p0 (pred_N n0)};
   XH ->
    case n of {
     N0 -> True;
     Npos p0 -> False}}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op plus x (S O)

of_nat :: Nat -> Positive
of_nat n =
  case n of {
   O -> XH;
   S x ->
    case x of {
     O -> XH;
     S n0 -> succ (of_nat x)}}

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ (of_succ_nat x)}

eq_dec :: Positive -> Positive -> Sumbool
eq_dec x y =
  positive_rec (\p h y0 ->
    case y0 of {
     XI p0 -> sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0);
     _ -> Right}) (\p h y0 ->
    case y0 of {
     XO p0 -> sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0);
     _ -> Right}) (\y0 ->
    case y0 of {
     XH -> Left;
     _ -> Right}) x y

peano_rect :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rect a f p =
  let {f2 = peano_rect (f XH a) (\p0 x -> f (succ (XO p0)) (f (XO p0) x))} in
  case p of {
   XI q -> f (XO q) (f2 q);
   XO q -> f2 q;
   XH -> a}

peano_rec :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Positive PeanoView

peanoView_rect :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                  PeanoView -> a1
peanoView_rect f f0 p p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p1 p2 -> f0 p1 p2 (peanoView_rect f f0 p1 p2)}

peanoView_rec :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                 PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Positive -> PeanoView -> PeanoView
peanoView_xO p q =
  case q of {
   PeanoOne -> PeanoSucc XH PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc (succ (XO p0)) (PeanoSucc (XO p0)
    (peanoView_xO p0 q0))}

peanoView_xI :: Positive -> PeanoView -> PeanoView
peanoView_xI p q =
  case q of {
   PeanoOne -> PeanoSucc (succ XH) (PeanoSucc XH PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc (succ (XI p0)) (PeanoSucc (XI p0)
    (peanoView_xI p0 q0))}

peanoView :: Positive -> PeanoView
peanoView p =
  case p of {
   XI p0 -> peanoView_xI p0 (peanoView p0);
   XO p0 -> peanoView_xO p0 (peanoView p0);
   XH -> PeanoOne}

peanoView_iter :: a1 -> (Positive -> a1 -> a1) -> Positive -> PeanoView -> a1
peanoView_iter a f p q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Positive -> Positive -> Reflect
eqb_spec x y =
  iff_reflect (eqb x y)

switch_Eq :: Comparison -> Comparison -> Comparison
switch_Eq c c' =
  case c' of {
   Eq -> c;
   x -> x}

mask2cmp :: Mask -> Comparison
mask2cmp p =
  case p of {
   IsNul -> Eq;
   IsPos p0 -> Gt;
   IsNeg -> Lt}

leb_spec0 :: Positive -> Positive -> Reflect
leb_spec0 x y =
  iff_reflect (leb x y)

ltb_spec0 :: Positive -> Positive -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb x y)

max_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max n m) __ (hl __);
   _ -> compat m (max n m) __ (hr __)}

max_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: Positive -> Positive -> Sumbool
max_dec n m =
  max_case n m (\x y _ h0 -> h0) Left Right

min_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min n m) __ (hr __);
   _ -> compat n (min n m) __ (hl __)}

min_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: Positive -> Positive -> Sumbool
min_dec n m =
  min_case n m (\x y _ h0 -> h0) Left Right

max_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case0 :: Positive -> Positive -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: Positive -> Positive -> Sumbool
max_dec0 =
  max_dec

min_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case0 :: Positive -> Positive -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: Positive -> Positive -> Sumbool
min_dec0 =
  min_dec

type T0 = N

zero :: N
zero =
  N0

one :: N
one =
  Npos XH

two :: N
two =
  Npos (XO XH)

succ_double :: N -> N
succ_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

double :: N -> N
double n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

succ0 :: N -> N
succ0 n =
  case n of {
   N0 -> Npos XH;
   Npos p -> Npos (succ p)}

pred0 :: N -> N
pred0 n =
  case n of {
   N0 -> N0;
   Npos p -> pred_N p}

succ_pos :: N -> Positive
succ_pos n =
  case n of {
   N0 -> XH;
   Npos p -> succ p}

add0 :: N -> N -> N
add0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (add p q)}}

sub0 :: N -> N -> N
sub0 n m =
  case n of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n;
     Npos m' ->
      case sub_mask n' m' of {
       IsPos p -> Npos p;
       _ -> N0}}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> Npos (mul p q)}}

compare0 :: N -> N -> Comparison
compare0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Eq;
     Npos m' -> Lt};
   Npos n' ->
    case m of {
     N0 -> Gt;
     Npos m' -> compare n' m'}}

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
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb0 :: N -> N -> Bool
ltb0 x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

min0 :: N -> N -> N
min0 n n' =
  case compare0 n n' of {
   Gt -> n';
   _ -> n}

max0 :: N -> N -> N
max0 n n' =
  case compare0 n n' of {
   Gt -> n;
   _ -> n'}

div0 :: N -> N
div0 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    case p0 of {
     XI p -> Npos p;
     XO p -> Npos p;
     XH -> N0}}

even :: N -> Bool
even n =
  case n of {
   N0 -> True;
   Npos p ->
    case p of {
     XO p0 -> True;
     _ -> False}}

odd :: N -> Bool
odd n =
  negb (even n)

pow0 :: N -> N -> N
pow0 n p =
  case p of {
   N0 -> Npos XH;
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
    case p0 of {
     XI p -> Npos (size p);
     XO p -> Npos (size p);
     XH -> N0}}

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

pos_div_eucl :: Positive -> N -> Prod N N
pos_div_eucl a b =
  case a of {
   XI a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub0 r' b);
       False -> Pair (double q) r'}};
   XO a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub0 r' b);
       False -> Pair (double q) r'}};
   XH ->
    case b of {
     N0 -> Pair N0 (Npos XH);
     Npos p ->
      case p of {
       XH -> Pair (Npos XH) N0;
       _ -> Pair N0 (Npos XH)}}}

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
   N0 -> Pair b (Pair N0 (Npos XH));
   Npos p ->
    case b of {
     N0 -> Pair a (Pair (Npos XH) N0);
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

discr :: N -> Sumor Positive
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
  case compare0 N0 a of {
   Lt -> succ0 (sqrt0 (pred0 a));
   _ -> N0}

log2_up :: N -> N
log2_up a =
  case compare0 (Npos XH) a of {
   Lt -> succ0 (log2 (pred0 a));
   _ -> N0}

lcm :: N -> N -> N
lcm a b =
  mul0 a (div b (gcd0 a b))

eqb_spec0 :: N -> N -> Reflect
eqb_spec0 x y =
  iff_reflect (eqb0 x y)

b2n :: Bool -> N
b2n b =
  case b of {
   True -> Npos XH;
   False -> N0}

setbit :: N -> N -> N
setbit a n =
  lor0 a (shiftl0 (Npos XH) n)

clearbit :: N -> N -> N
clearbit a n =
  ldiff0 a (shiftl0 (Npos XH) n)

ones :: N -> N
ones n =
  pred0 (shiftl0 (Npos XH) n)

lnot :: N -> N -> N
lnot a n =
  lxor0 a (ones n)

max_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat n (max0 n m) __ (hl __);
   _ -> compat m (max0 n m) __ (hr __)}

max_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case1 n m x x0 x1 =
  max_case_strong1 n m x (\_ -> x0) (\_ -> x1)

max_dec1 :: N -> N -> Sumbool
max_dec1 n m =
  max_case1 n m (\x y _ h0 -> h0) Left Right

min_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

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

type T1 = Z

zero0 :: Z
zero0 =
  Z0

one0 :: Z
one0 =
  Zpos XH

two0 :: Z
two0 =
  Zpos (XO XH)

double0 :: Z -> Z
double0 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double0 :: Z -> Z
succ_double0 x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double0 (pos_sub p q);
     XO q -> succ_double0 (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double0 (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add1 :: Z -> Z -> Z
add1 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add x' y')}}

opp :: Z -> Z
opp x =
  case x of {
   Z0 -> Z0;
   Zpos x0 -> Zneg x0;
   Zneg x0 -> Zpos x0}

succ1 :: Z -> Z
succ1 x =
  add1 x (Zpos XH)

pred1 :: Z -> Z
pred1 x =
  add1 x (Zneg XH)

sub1 :: Z -> Z -> Z
sub1 m n =
  add1 m (opp n)

mul1 :: Z -> Z -> Z
mul1 x y =
  case x of {
   Z0 -> Z0;
   Zpos x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zpos (mul x' y');
     Zneg y' -> Zneg (mul x' y')};
   Zneg x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zneg (mul x' y');
     Zneg y' -> Zpos (mul x' y')}}

pow_pos :: Z -> Positive -> Z
pow_pos z n =
  iter n (mul1 z) (Zpos XH)

pow1 :: Z -> Z -> Z
pow1 x y =
  case y of {
   Z0 -> Zpos XH;
   Zpos p -> pow_pos x p;
   Zneg p -> Z0}

square1 :: Z -> Z
square1 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (square p);
   Zneg p -> Zpos (square p)}

compare1 :: Z -> Z -> Comparison
compare1 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> Eq;
     Zpos y' -> Lt;
     Zneg y' -> Gt};
   Zpos x' ->
    case y of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

sgn :: Z -> Z
sgn z =
  case z of {
   Z0 -> Z0;
   Zpos p -> Zpos XH;
   Zneg p -> Zneg XH}

leb1 :: Z -> Z -> Bool
leb1 x y =
  case compare1 x y of {
   Gt -> False;
   _ -> True}

ltb1 :: Z -> Z -> Bool
ltb1 x y =
  case compare1 x y of {
   Lt -> True;
   _ -> False}

geb :: Z -> Z -> Bool
geb x y =
  case compare1 x y of {
   Lt -> False;
   _ -> True}

gtb :: Z -> Z -> Bool
gtb x y =
  case compare1 x y of {
   Gt -> True;
   _ -> False}

eqb1 :: Z -> Z -> Bool
eqb1 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> True;
     _ -> False};
   Zpos p ->
    case y of {
     Zpos q -> eqb p q;
     _ -> False};
   Zneg p ->
    case y of {
     Zneg q -> eqb p q;
     _ -> False}}

max1 :: Z -> Z -> Z
max1 n m =
  case compare1 n m of {
   Lt -> m;
   _ -> n}

min1 :: Z -> Z -> Z
min1 n m =
  case compare1 n m of {
   Gt -> m;
   _ -> n}

abs :: Z -> Z
abs z =
  case z of {
   Zneg p -> Zpos p;
   x -> x}

abs_nat :: Z -> Nat
abs_nat z =
  case z of {
   Z0 -> O;
   Zpos p -> to_nat p;
   Zneg p -> to_nat p}

abs_N :: Z -> N
abs_N z =
  case z of {
   Z0 -> N0;
   Zpos p -> Npos p;
   Zneg p -> Npos p}

to_nat1 :: Z -> Nat
to_nat1 z =
  case z of {
   Zpos p -> to_nat p;
   _ -> O}

to_N :: Z -> N
to_N z =
  case z of {
   Zpos p -> Npos p;
   _ -> N0}

of_nat1 :: Nat -> Z
of_nat1 n =
  case n of {
   O -> Z0;
   S n0 -> Zpos (of_succ_nat n0)}

of_N :: N -> Z
of_N n =
  case n of {
   N0 -> Z0;
   Npos p -> Zpos p}

to_pos :: Z -> Positive
to_pos z =
  case z of {
   Zpos p -> p;
   _ -> XH}

iter1 :: Z -> (a1 -> a1) -> a1 -> a1
iter1 n f x =
  case n of {
   Zpos p -> iter p f x;
   _ -> x}

pos_div_eucl0 :: Positive -> Z -> Prod Z Z
pos_div_eucl0 a b =
  case a of {
   XI a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = add1 (mul1 (Zpos (XO XH)) r) (Zpos XH)} in
      case ltb1 r' b of {
       True -> Pair (mul1 (Zpos (XO XH)) q) r';
       False -> Pair (add1 (mul1 (Zpos (XO XH)) q) (Zpos XH)) (sub1 r' b)}};
   XO a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = mul1 (Zpos (XO XH)) r} in
      case ltb1 r' b of {
       True -> Pair (mul1 (Zpos (XO XH)) q) r';
       False -> Pair (add1 (mul1 (Zpos (XO XH)) q) (Zpos XH)) (sub1 r' b)}};
   XH ->
    case leb1 (Zpos (XO XH)) b of {
     True -> Pair Z0 (Zpos XH);
     False -> Pair (Zpos XH) Z0}}

div_eucl0 :: Z -> Z -> Prod Z Z
div_eucl0 a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos p -> pos_div_eucl0 a' b;
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add1 q (Zpos XH))) (add1 b r)}}};
   Zneg a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos p ->
      case pos_div_eucl0 a' b of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add1 q (Zpos XH))) (sub1 b r)}};
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       Pair q r -> Pair q (opp r)}}}

div1 :: Z -> Z -> Z
div1 a b =
  case div_eucl0 a b of {
   Pair q x -> q}

modulo0 :: Z -> Z -> Z
modulo0 a b =
  case div_eucl0 a b of {
   Pair x r -> r}

quotrem :: Z -> Z -> Prod Z Z
quotrem a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a0 ->
    case b of {
     Z0 -> Pair Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (of_N r)};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (of_N r)}};
   Zneg a0 ->
    case b of {
     Z0 -> Pair Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (opp (of_N r))};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (opp (of_N r))}}}

quot :: Z -> Z -> Z
quot a b =
  fst (quotrem a b)

rem :: Z -> Z -> Z
rem a b =
  snd (quotrem a b)

even0 :: Z -> Bool
even0 z =
  case z of {
   Z0 -> True;
   Zpos p ->
    case p of {
     XO p0 -> True;
     _ -> False};
   Zneg p ->
    case p of {
     XO p0 -> True;
     _ -> False}}

odd0 :: Z -> Bool
odd0 z =
  case z of {
   Z0 -> False;
   Zpos p ->
    case p of {
     XO p0 -> False;
     _ -> True};
   Zneg p ->
    case p of {
     XO p0 -> False;
     _ -> True}}

div3 :: Z -> Z
div3 z =
  case z of {
   Z0 -> Z0;
   Zpos p ->
    case p of {
     XH -> Z0;
     _ -> Zpos (div2 p)};
   Zneg p -> Zneg (div2_up p)}

quot2 :: Z -> Z
quot2 z =
  case z of {
   Z0 -> Z0;
   Zpos p ->
    case p of {
     XH -> Z0;
     _ -> Zpos (div2 p)};
   Zneg p ->
    case p of {
     XH -> Z0;
     _ -> Zneg (div2 p)}}

log0 :: Z -> Z
log0 z =
  case z of {
   Zpos p0 ->
    case p0 of {
     XI p -> Zpos (size p);
     XO p -> Zpos (size p);
     XH -> Z0};
   _ -> Z0}

sqrtrem1 :: Z -> Prod Z Z
sqrtrem1 n =
  case n of {
   Zpos p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair (Zpos s) (Zpos r);
       _ -> Pair (Zpos s) Z0}};
   _ -> Pair Z0 Z0}

sqrt1 :: Z -> Z
sqrt1 n =
  case n of {
   Zpos p -> Zpos (sqrt p);
   _ -> Z0}

gcd1 :: Z -> Z -> Z
gcd1 a b =
  case a of {
   Z0 -> abs b;
   Zpos a0 ->
    case b of {
     Z0 -> abs a;
     Zpos b0 -> Zpos (gcd a0 b0);
     Zneg b0 -> Zpos (gcd a0 b0)};
   Zneg a0 ->
    case b of {
     Z0 -> abs a;
     Zpos b0 -> Zpos (gcd a0 b0);
     Zneg b0 -> Zpos (gcd a0 b0)}}

ggcd1 :: Z -> Z -> Prod Z (Prod Z Z)
ggcd1 a b =
  case a of {
   Z0 -> Pair (abs b) (Pair Z0 (sgn b));
   Zpos a0 ->
    case b of {
     Z0 -> Pair (abs a) (Pair (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zpos aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zpos aa) (Zneg bb))}}};
   Zneg a0 ->
    case b of {
     Z0 -> Pair (abs a) (Pair (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zneg aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zneg aa) (Zneg bb))}}}}

testbit1 :: Z -> Z -> Bool
testbit1 a n =
  case n of {
   Z0 -> odd0 a;
   Zpos p ->
    case a of {
     Z0 -> False;
     Zpos a0 -> testbit a0 (Npos p);
     Zneg a0 -> negb (testbit0 (pred_N a0) (Npos p))};
   Zneg p -> False}

shiftl1 :: Z -> Z -> Z
shiftl1 a n =
  case n of {
   Z0 -> a;
   Zpos p -> iter p (mul1 (Zpos (XO XH))) a;
   Zneg p -> iter p div3 a}

shiftr1 :: Z -> Z -> Z
shiftr1 a n =
  shiftl1 a (opp n)

lor1 :: Z -> Z -> Z
lor1 a b =
  case a of {
   Z0 -> b;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zpos (lor a0 b0);
     Zneg b0 -> Zneg (succ_pos (ldiff0 (pred_N b0) (Npos a0)))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (ldiff0 (pred_N a0) (Npos b0)));
     Zneg b0 -> Zneg (succ_pos (land0 (pred_N a0) (pred_N b0)))}}

land1 :: Z -> Z -> Z
land1 a b =
  case a of {
   Z0 -> Z0;
   Zpos a0 ->
    case b of {
     Z0 -> Z0;
     Zpos b0 -> of_N (land a0 b0);
     Zneg b0 -> of_N (ldiff0 (Npos a0) (pred_N b0))};
   Zneg a0 ->
    case b of {
     Z0 -> Z0;
     Zpos b0 -> of_N (ldiff0 (Npos b0) (pred_N a0));
     Zneg b0 -> Zneg (succ_pos (lor0 (pred_N a0) (pred_N b0)))}}

ldiff1 :: Z -> Z -> Z
ldiff1 a b =
  case a of {
   Z0 -> Z0;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> of_N (ldiff a0 b0);
     Zneg b0 -> of_N (land0 (Npos a0) (pred_N b0))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (lor0 (pred_N a0) (Npos b0)));
     Zneg b0 -> of_N (ldiff0 (pred_N b0) (pred_N a0))}}

lxor1 :: Z -> Z -> Z
lxor1 a b =
  case a of {
   Z0 -> b;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> of_N (lxor a0 b0);
     Zneg b0 -> Zneg (succ_pos (lxor0 (Npos a0) (pred_N b0)))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (lxor0 (pred_N a0) (Npos b0)));
     Zneg b0 -> of_N (lxor0 (pred_N a0) (pred_N b0))}}

eq_dec1 :: Z -> Z -> Sumbool
eq_dec1 x y =
  z_rec (\y0 ->
    case y0 of {
     Z0 -> Left;
     _ -> Right}) (\p y0 ->
    case y0 of {
     Zpos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0);
     _ -> Right}) (\p y0 ->
    case y0 of {
     Zneg p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0);
     _ -> Right}) x y

leb_spec2 :: Z -> Z -> Reflect
leb_spec2 x y =
  iff_reflect (leb1 x y)

ltb_spec2 :: Z -> Z -> Reflect
ltb_spec2 x y =
  iff_reflect (ltb1 x y)

sqrt_up0 :: Z -> Z
sqrt_up0 a =
  case compare1 Z0 a of {
   Lt -> succ1 (sqrt1 (pred1 a));
   _ -> Z0}

log2_up0 :: Z -> Z
log2_up0 a =
  case compare1 (Zpos XH) a of {
   Lt -> succ1 (log0 (pred1 a));
   _ -> Z0}

div4 :: Z -> Z -> Z
div4 =
  quot

modulo1 :: Z -> Z -> Z
modulo1 =
  rem

lcm0 :: Z -> Z -> Z
lcm0 a b =
  abs (mul1 a (div1 b (gcd1 a b)))

eqb_spec1 :: Z -> Z -> Reflect
eqb_spec1 x y =
  iff_reflect (eqb1 x y)

b2z :: Bool -> Z
b2z b =
  case b of {
   True -> Zpos XH;
   False -> Z0}

setbit0 :: Z -> Z -> Z
setbit0 a n =
  lor1 a (shiftl1 (Zpos XH) n)

clearbit0 :: Z -> Z -> Z
clearbit0 a n =
  ldiff1 a (shiftl1 (Zpos XH) n)

lnot0 :: Z -> Z
lnot0 a =
  pred1 (opp a)

ones0 :: Z -> Z
ones0 n =
  pred1 (shiftl1 (Zpos XH) n)

max_case_strong3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat n (max1 n m) __ (hl __);
   _ -> compat m (max1 n m) __ (hr __)}

max_case3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case3 n m x x0 x1 =
  max_case_strong3 n m x (\_ -> x0) (\_ -> x1)

max_dec3 :: Z -> Z -> Sumbool
max_dec3 n m =
  max_case3 n m (\x y _ h0 -> h0) Left Right

min_case_strong3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat m (min1 n m) __ (hr __);
   _ -> compat n (min1 n m) __ (hl __)}

min_case3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case3 n m x x0 x1 =
  min_case_strong3 n m x (\_ -> x0) (\_ -> x1)

min_dec3 :: Z -> Z -> Sumbool
min_dec3 n m =
  min_case3 n m (\x y _ h0 -> h0) Left Right

max_case_strong4 :: Z -> Z -> (() -> a1) -> (() -> a1) -> a1
max_case_strong4 n m x x0 =
  max_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case4 :: Z -> Z -> a1 -> a1 -> a1
max_case4 n m x x0 =
  max_case_strong4 n m (\_ -> x) (\_ -> x0)

max_dec4 :: Z -> Z -> Sumbool
max_dec4 =
  max_dec3

min_case_strong4 :: Z -> Z -> (() -> a1) -> (() -> a1) -> a1
min_case_strong4 n m x x0 =
  min_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case4 :: Z -> Z -> a1 -> a1 -> a1
min_case4 n m x x0 =
  min_case_strong4 n m (\_ -> x) (\_ -> x0)

min_dec4 :: Z -> Z -> Sumbool
min_dec4 =
  min_dec3

z_lt_dec :: Z -> Z -> Sumbool
z_lt_dec x y =
  case compare1 x y of {
   Lt -> Left;
   _ -> Right}

z_lt_ge_dec :: Z -> Z -> Sumbool
z_lt_ge_dec x y =
  z_lt_dec x y

z_lt_le_dec :: Z -> Z -> Sumbool
z_lt_le_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_lt_ge_dec x y)

data Q =
   Qmake Z Positive

qnum :: Q -> Z
qnum q =
  case q of {
   Qmake qnum0 qden0 -> qnum0}

qden :: Q -> Positive
qden q =
  case q of {
   Qmake qnum0 qden0 -> qden0}

qplus :: Q -> Q -> Q
qplus x y =
  Qmake
    (add1 (mul1 (qnum x) (Zpos (qden y))) (mul1 (qnum y) (Zpos (qden x))))
    (mul (qden x) (qden y))

qmult :: Q -> Q -> Q
qmult x y =
  Qmake (mul1 (qnum x) (qnum y)) (mul (qden x) (qden y))

qopp :: Q -> Q
qopp x =
  Qmake (opp (qnum x)) (qden x)

qminus :: Q -> Q -> Q
qminus x y =
  qplus x (qopp y)

qinv :: Q -> Q
qinv x =
  case qnum x of {
   Z0 -> Qmake Z0 XH;
   Zpos p -> Qmake (Zpos (qden x)) p;
   Zneg p -> Qmake (Zneg (qden x)) p}

qdiv :: Q -> Q -> Q
qdiv x y =
  qmult x (qinv y)

qlt_le_dec :: Q -> Q -> Sumbool
qlt_le_dec x y =
  z_lt_le_dec (mul1 (qnum x) (Zpos (qden y))) (mul1 (qnum y) (Zpos (qden x)))

qred :: Q -> Q
qred q =
  case q of {
   Qmake q1 q2 ->
    case snd (ggcd1 q1 (Zpos q2)) of {
     Pair r1 r2 -> Qmake r1 (to_pos r2)}}

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

type Ballot cand = Prod (List cand) Q

data FT_Judgement cand =
   State (Prod
         (Prod
         (Prod
         (Prod (Prod (List (Ballot cand)) (cand -> Q))
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

sum :: (List a1) -> (List (Ballot a1)) -> Q
sum cand_all0 l =
  case l of {
   Nil -> Qmake Z0 XH;
   Cons l0 ls -> qred (qplus (snd l0) (sum cand_all0 ls))}

eq_dec_nat :: Nat -> Nat -> Sumbool
eq_dec_nat n m =
  let {h = lt_eq_lt_dec n m} in
  case h of {
   Inleft h2 ->
    case h2 of {
     Left -> Right;
     Right -> Left};
   Inright -> Right}

fTR :: (List a1) -> (a1 -> (List a1) -> Sumbool) -> Nat -> Q -> List
       (FT_Rule a1)
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

list_min :: (List a1) -> (a1 -> Q) -> Sum () (SigT a1 ())
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

update_pile :: (List a1) -> (a1 -> (List a1) -> Sumbool) -> Q -> (a1 -> List
               (Ballot a1)) -> (a1 -> Q) -> (List a1) -> a1 -> List
               (Ballot a1)
update_pile cand_all0 cand_in_dec qu0 p t l c =
  case cand_in_dec c l of {
   Left ->
    map (\b -> Pair (fst b)
      (qred (qmult (snd b) (qdiv (qminus (t c) qu0) (t c))))) (p c);
   Right -> p c}

emp :: (List a1) -> (a1 -> a1 -> Sumbool) -> a1 -> (a1 -> List (Ballot a1))
       -> a1 -> List (Ballot a1)
emp cand_all0 cand_eq_dec c p d =
  case cand_eq_dec c d of {
   Left -> Nil;
   Right -> p d}

extend_ordered_type :: (a1 -> Q) -> (List a1) -> a1 -> SigT (List a1)
                       (SigT (List a1) ())
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

list_max :: (List a1) -> (a1 -> Q) -> Sum () (SigT a1 ())
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

list_max_cor :: (List a1) -> (a1 -> Q) -> SigT a1 ()
list_max_cor l f =
  let {h0 = list_max l f} in
  case h0 of {
   Inl _ -> false_rect;
   Inr s -> s}

constructing_electable_first :: (a1 -> a1 -> Sumbool) -> (a1 -> (List 
                                a1) -> Sumbool) -> Nat -> Q -> (List a1) ->
                                (a1 -> Q) -> (List a1) -> SigT (List a1) 
                                ()
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
          -> Nat -> Q -> (FT_Judgement a1) -> SigT (Rule (FT_Judgement a1))
          (SigT (FT_Judgement a1) ())
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
                     Cons c bl -> ExistT __ (ExistT
                      (case eq_dec_nat (length (proj1_sig x0)) st0 of {
                        Left -> Winners (proj1_sig x0);
                        Right -> State (Pair (Pair (Pair (Pair (Pair 
                         (x2 c) t) (emp cand_all0 cand_eq_dec c x2)) bl) x0)
                         x)}) __)};
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
 | D
 | E
 | F
 | G
 | H
 | I
 | J
 | K
 | L
 | M
 | N1
 | O0
 | P
 | Q0
 | R
 | S0
 | T2 
 | A0
 | B0
 | C0
 | D0
 | E0
 | F0
 | G0
 | H0
 | I0
 | J0
 | K0
 | L0
 | M0
 | N10
 | O00
 | P0
 | Q00
 |A1
 |B1
 |C1
--}



cand_all :: List Cand
cand_all =
 Cons A (Cons B (Cons C (Cons D (Cons E (Cons F (Cons G (Cons H (Cons I
    (Cons J (Cons K (Cons L (Cons M (Cons N1 (Cons O0 (Cons P (Cons Q0 (Cons
    R (Cons S0 (Cons T2 (Cons A0 (Cons B0 (Cons C0 (Cons D0 (Cons E0 (Cons F0 (Cons G0 (Cons H0 (Cons I0 (Cons J0 (Cons K0 (Cons L0 (Cons M0 (Cons N10 (Cons O00 (Cons P0 (Cons Q00 (Cons A1 (Cons B1 (Cons C1 Nil)))))))))))))))))))))))))))))))))))))))

--}

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
     _ -> Right};
   D ->
    case d of {
     D -> Left;
     _ -> Right};
   E ->
    case d of {
     E -> Left;
     _ -> Right};
   F ->
    case d of {
     F -> Left;
     _ -> Right};
   G ->
    case d of {
     G -> Left;
     _ -> Right};
   H ->
    case d of {
     H -> Left;
     _ -> Right};
   I ->
    case d of {
     I -> Left;
     _ -> Right};
   J ->
    case d of {
     J -> Left;
     _ -> Right};
   K ->
    case d of {
     K -> Left;
     _ -> Right};
   L ->
    case d of {
     L -> Left;
     _ -> Right};
   M ->
    case d of {
     M -> Left;
     _ -> Right};
   N1 ->
    case d of {
     N1 -> Left;
     _ -> Right};
   O0 ->
    case d of {
     O0 -> Left;
     _ -> Right};
   P ->
    case d of {
     P -> Left;
     _ -> Right};
   Q0 ->
    case d of {
     Q0 -> Left;
     _ -> Right};
   R ->
    case d of {
     R -> Left;
     _ -> Right};
   S0 ->
    case d of {
     S0 -> Left;
     _ -> Right};
   T2 ->
    case d of {
     T2 -> Left;
     _ -> Right};
   A0 ->
    case d of {
     A0 -> Left;
     _ -> Right};
   B0 ->
    case d of {
     B0 -> Left;
     _ -> Right};
   C0 ->
    case d of {
     C0 -> Left;
     _ -> Right};
   D0 ->
    case d of {
     D0 -> Left;
     _ -> Right};
   E0 ->
    case d of {
     E0 -> Left;
     _ -> Right};
   F0 ->
    case d of {
     F0 -> Left;
     _ -> Right};
   G0 ->
    case d of {
     G0 -> Left;
     _ -> Right};
   H0 ->
    case d of {
     H0 -> Left;
     _ -> Right};
   I0 ->
    case d of {
     I0 -> Left;
     _ -> Right};
   J0 ->
    case d of {
     J0 -> Left;
     _ -> Right};
   K0 ->
    case d of {
     K0 -> Left;
     _ -> Right};
   L0 ->
    case d of {
     L0 -> Left;
     _ -> Right};
   M0 ->
    case d of {
     M0 -> Left;
     _ -> Right};
   N10 ->
    case d of {
     N10 -> Left;
     _ -> Right};
   O00 ->
    case d of {
     O00 -> Left;
     _ -> Right};
   P0 ->
    case d of {
     P0 -> Left;
     _ -> Right};
   Q00 ->
    case d of {
     Q00 -> Left;
     _ -> Right};
   A1 -> 
    case d of {
     A1 -> Left;
     _ -> Right};
   B1 ->
    case d of {
     B1 -> Left;
     _ -> Right};
   C1 ->
    case d of {
     C1 -> Left;
     _ -> Right}} 

--}

listdec :: Cand -> (List Cand) -> Sumbool
listdec c l =
  in_dec canddec c l

qu :: Q
qu = 
 Qmake (Zpos (XO (XI (XO (XI (XO (XO (XO (XO XH))))))))) (XO (XO (XI (XO (XO (XI XH))))))

st :: Nat
st =
  S (S O) 

hunion_count :: (FT_Judgement Cand) -> SigT (FT_Judgement Cand)
                (Prod () (Pf (FT_Judgement Cand)))
hunion_count =
  termination (final_dec cand_all st) (fT_m cand_all st)
    (fTR cand_all listdec st qu) (\x _ ->
    app_FT cand_all canddec listdec st qu x)

