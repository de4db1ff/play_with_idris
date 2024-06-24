module Lab12

import Data.Fin

%default total

And : Type -> Type -> Type
And = Pair

Or : Type -> Type -> Type
Or = Either

Not' : Type -> Type
Not' a = a -> Void

Implies : Type -> Type -> Type
Implies a b = a -> b

Exists : (t : Type) -> (p : t -> Type) -> Type
Exists = DPair

Forall : (t : Type) -> (p : t -> Type) -> Type
Forall t p = (x : t) -> p x

and_comm : And p q -> And q p
and_comm x = (snd x, fst x)

and_assoc : (p `And` q) `And` r -> p `And` (q `And` r)
and_assoc x = (fst (fst x), (snd (fst x), snd x))

or_comm : Or p q -> Or q p
or_comm (Left x) = Right x
or_comm (Right x) = Left x

or_assoc : (p `Or` q) `Or` r -> p `Or` (q `Or` r)
or_assoc (Left (Left x)) = Left x
or_assoc (Left (Right x)) = Right (Left x)
or_assoc (Right x) = Right (Right x)

and_distr : p `And` (q `Or` r) -> (p `And` q) `Or` (p `And` r)
and_distr (x, (Left y)) = Left (x, y)
and_distr (x, (Right y)) = Right (x, y)

modus_ponens : (a `Implies` b) `And` a -> b
modus_ponens (x, y) = x y

implies_implies : (a `And` b) `Implies` c -> a `Implies` (b `Implies` c)
implies_implies f x y = f (x, y)

implies_and : a `Implies` (b `And` c) -> (a `Implies` b) `And` (a `Implies` c)
implies_and f = (fst . f, snd . f)

implies_or : (a `Implies` c) `And` (b `Implies` c) -> (a `Or` b) `Implies` c
implies_or (x, z) (Left y) = x y
implies_or (x, z) (Right y) = z y

contraposition : a `Implies` b -> (Not b `Implies` Not a)
contraposition f g x = g (f x)

law_of_excluded_middle : p `Or` (Not p)
law_of_excluded_middle = ?law_of_excluded_middle_rhs
-- it is not possible to proof this in idris (constructive logic) as this problem is equivalent to the halting problem (predict the truth value of any given `p` in finite time)

double_negation : Not (Not a) -> a
-- unprovable 

double_negation_intro : a -> Not (Not a)
double_negation_intro x f = f x


triple_negation_elim : Not (Not (Not a)) -> Not a
triple_negation_elim f x = f (\y => y x)

exist_and : Exists t (\x => p x `And` q x) -> (Exists t p `And` Exists t q)
exist_and (v ** (x, y)) = ((v ** x), (v ** y))

not_exists : Exists t p -> Not (Forall t (\x => Not (p x)))
not_exists (fst ** snd) f = f fst snd

exists_forall_then_forall_exists : {p : a -> b -> Type} -> Exists a (\x => Forall b (\y => p x y)) -> Forall b (\y => Exists a (\x => p x y))
exists_forall_then_forall_exists (fst ** snd) x = (fst ** snd x)

