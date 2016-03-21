{-# LANGUAGE StandaloneDeriving, UnicodeSyntax, LambdaCase, RankNTypes, DeriveFunctor, ViewPatterns, OverloadedStrings #-}

module Presburger where

import Prelude hiding (negate)
import Data.String
import Data.List
import Data.Bool
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Set.Unicode
import Control.Monad

type Variable = String
type Constant = Integer

data Term = Constant :* Term
          | Term :+ Term
          | Term :- Term
          | C Constant
          | V Variable

data CTerm = CT (Map Variable Constant) Constant

data Formula a = TRUE | FALSE
               | Formula a :/\ Formula a
               | Formula a :\/ Formula a
               | Not (Formula a)
               | Forall Variable (Formula a)
               | Exists Variable (Formula a)
               | Atom a

(==>), (<=>) :: Formula a -> Formula a -> Formula a
(==>) p q = Not p :\/ q
(<=>) p q = p ==> q :/\ q ==> p

boolToFormula :: Bool -> Formula a
boolToFormula = bool FALSE TRUE

data Atom = Term :< Term
          | Term :<= Term
          | Term :== Term
          | Term :>= Term
          | Term :> Term
          | Constant :| Term

data CAtom = EqualZero CTerm
           | GreaterZero CTerm
           | Divides Constant CTerm

constCTerm :: Constant -> CTerm
constCTerm = CT Map.empty

varCTerm :: Variable -> CTerm
varCTerm v = CT (Map.singleton v 1) 0

zero, one :: CTerm
zero = constCTerm 0
one  = constCTerm 1

(.*) :: Constant -> CTerm -> CTerm
0 .* _ = zero
n .* CT coeffs k =
  CT ((n *) <$> coeffs) (n * k)

(.+), (.-) :: CTerm -> CTerm -> CTerm
CT coeffs1 k1 .+ CT coeffs2 k2 =
  CT (Map.unionWith (+) coeffs1 coeffs2) (k1 + k2)
t .- s = t .+ (-1) .* s

getCanonTerm :: CAtom -> CTerm
getCanonTerm = \case
  Divides _   t -> t
  EqualZero   t -> t
  GreaterZero t -> t

setCanonTerm :: CAtom -> CTerm -> CAtom
setCanonTerm = \case
  Divides d   _ -> Divides d
  GreaterZero _ -> GreaterZero
  EqualZero   _ -> EqualZero

canonAtom :: Atom -> CAtom
canonAtom = \case
  (k :|  s) -> Divides (abs k) (canonTerm s)
  (s :== t) -> EqualZero   $ canonTerm t .- canonTerm s
  (s :<  t) -> GreaterZero $ canonTerm t .- canonTerm s
  (s :>  t) -> canonAtom (t :< s)
  (s :<= t) -> canonAtom (s :< t :+ C 1)
  (s :>= t) -> canonAtom (s :> t :- C 1)

canonTerm :: Term -> CTerm
canonTerm = \case
  (k :* t) -> k .* canonTerm t
  (s :+ t) -> canonTerm s .+ canonTerm t
  (s :- t) -> canonTerm s .- canonTerm t
  (C c)    -> constCTerm c
  (V v)    -> varCTerm v

uncanonAtom :: CAtom -> Atom
uncanonAtom = \case
  Divides d t   -> d :| uncanonTerm t
  EqualZero t   -> (C 0 :== uncanonTerm t)
  GreaterZero t -> (C 0 :<  uncanonTerm t)

uncanonTerm :: CTerm -> Term
uncanonTerm (CT m k) =
  foldr (:+) (C k) . map (\(v,c) -> c :* V v) $ Map.assocs m

-- Rewrite a canonical formula to eliminate negation of inequality at the top level
posineq :: Formula CAtom -> Formula CAtom
posineq = \case
  Not (Atom (GreaterZero t)) ->
       Atom (GreaterZero (one .- t))
  fm -> fm

-- Apply a function to the atoms of a formula (yes, this is bind)
onAtoms :: (a -> Formula b) -> Formula a -> Formula b
onAtoms f = \case
  Not p      -> Not (onAtoms f p)
  p :/\  q   -> onAtoms f p :/\ onAtoms f q
  p :\/  q   -> onAtoms f p :\/ onAtoms f q
  Forall x p -> Forall x (onAtoms f p)
  Exists x p -> Exists x (onAtoms f p)
  Atom a     -> f a
  TRUE       -> TRUE
  FALSE      -> FALSE

-- Reduce a formula involving only constants
evalc :: Formula CAtom -> Formula CAtom
evalc = onAtoms $ either Atom boolToFormula . \case
  EqualZero   (CT m k) | Map.null m -> Right $ 0 == k
  GreaterZero (CT m k) | Map.null m -> Right $ 0 <  k
  Divides d   (CT m k) | Map.null m -> Right $ k `mod` d == 0
  atom -> Left atom

-- THE SOLVER: Integer quantifier elimination via Cooper's algorithm
integerQelim :: Formula Atom -> Formula Atom
integerQelim =
  fmap uncanonAtom . simplify . evalc
  . liftQelim canonAtom (cnnf posineq . evalc) cooper

-- The least common multiplier of x for all its occurrences in the formula
formlcm :: Variable -> Formula CAtom -> Integer
formlcm x = \case
  Atom (getCanonTerm -> CT (Map.lookup x -> Just c) _) -> abs c
  Not p -> formlcm x p
  p :/\ q -> formlcm x p `lcm` formlcm x q
  p :\/ q -> formlcm x p `lcm` formlcm x q
  _ -> 1

-- Adjust the coefficients of x so that they lie between -1 and 1, given the lcm for x
adjustcoeff :: Variable -> Integer -> Formula CAtom -> Formula CAtom
adjustcoeff x l = \case
  Atom t@(getCanonTerm -> CT (Map.lookup x -> Just c) (constCTerm -> z)) ->
    let m = l `div` c
        n = case t of
          GreaterZero {} -> abs m
          _              -> m
        xtm = (m `div` n) .* varCTerm x
    in
      Atom $
        (case t of
           Divides d   _ -> Divides (abs m * d)
           GreaterZero _ -> GreaterZero
           EqualZero   _ -> EqualZero)
        (xtm .+ n .* z)
  Not p   -> Not $ adjustcoeff x l p
  p :/\ q -> adjustcoeff x l p :/\ adjustcoeff x l q
  p :\/ q -> adjustcoeff x l p :\/ adjustcoeff x l q
  fm -> fm

-- Adjust the coefficients of x so that they lie between -1 and 1
unitycoeff :: Variable -> Formula CAtom -> Formula CAtom
unitycoeff x fm =
  let l = formlcm x fm
      fm' = adjustcoeff x l fm
  in
    if l == 1 then fm'
    else Atom (Divides l (varCTerm x)) :/\ fm'

-- The "minus infinity" transformation
minusinf :: Variable -> Formula CAtom -> Formula CAtom
minusinf x = \case
  Atom (EqualZero   (CT (Map.lookup x -> Just   1)  _)) -> FALSE
  Atom (GreaterZero (CT (Map.lookup x -> Just   1)  _)) -> FALSE
  Atom (GreaterZero (CT (Map.lookup x -> Just (-1)) _)) -> TRUE
  Not p -> Not (minusinf x p)
  p :/\ q -> minusinf x p :/\ minusinf x q
  p :\/ q -> minusinf x p :\/ minusinf x q
  fm -> fm

-- The least common denominator of all divisors in Divides x statements
divlcm :: Variable -> Formula CAtom -> Integer
divlcm x = \case
  Atom (Divides d (CT (Map.lookup x -> Just c) _)) -> d
  Not p -> divlcm x p
  p :/\ q -> divlcm x p `lcm` divlcm x q
  p :\/ q -> divlcm x p `lcm` divlcm x q
  _ -> 1

-- Compute the "boundary set" for a variable x in a formula
bset :: Variable -> Formula CAtom -> Set CTerm
bset x = \case
    Not (Atom (EqualZero (CT (Map.lookup x -> Just 1) (constCTerm -> a)))) -> Set.singleton $ (-1) .* a
    Atom      (EqualZero (CT (Map.lookup x -> Just 1) (constCTerm -> a)))  -> Set.singleton $ (-1) .* (a .+ one)
    Atom    (GreaterZero (CT (Map.lookup x -> Just 1) (constCTerm -> a)))  -> Set.singleton $ (-1) .* a
    Not p -> bset x p
    p :/\ q -> bset x p ∪ bset x q
    p :\/ q -> bset x p ∪ bset x q
    _ -> Set.empty

-- Replace a variable with a term in a formula
linrep :: Variable -> CTerm -> Formula CAtom -> Formula CAtom
linrep x t = \case
  Atom s@(getCanonTerm -> CT (Map.lookup x -> Just c) (constCTerm -> a)) ->
    Atom $ setCanonTerm s (c .* t .+ a)
  Not p -> Not (linrep x t p)
  p :/\ q -> linrep x t p :/\ linrep x t q
  p :\/ q -> linrep x t p :\/ linrep x t q
  fm -> fm

-- Cooper's algorithm
cooper :: Formula CAtom -> Formula CAtom
cooper (Exists x (unitycoeff x -> p)) =
  disjoin (map stage js)
  where
    p_inf = simplify $ minusinf x p
    bs = bset x p
    js = [1 .. divlcm x p]
    p_element j b = linrep x (b .+ constCTerm j) p
    stage j =
      disjoin $ linrep x (constCTerm j) p_inf :
                map (p_element j) (Set.toList bs)
cooper _ = error "cooper: not an existential formula"

-- Simplifying formulae

-- Recursively simplify the boolean bits of a formula
psimplify :: Formula a -> Formula a
psimplify = \case
  Not p      -> psimplify1 (Not (psimplify p))
  p :/\  q   -> psimplify1 (psimplify p :/\ psimplify q)
  p :\/  q   -> psimplify1 (psimplify p :\/ psimplify q)
  fm         -> fm

-- Simplify the boolean bits of a formula one level down
psimplify1 :: Formula a -> Formula a
psimplify1 = \case
  Not FALSE   -> TRUE
  Not TRUE    -> FALSE
  Not (Not p) -> p
  _ :/\ FALSE -> FALSE
  FALSE :/\ _ -> FALSE
  p :/\ TRUE  -> p
  TRUE :/\ p  -> p
  p :\/ FALSE -> p
  FALSE :\/ p -> p
  _ :\/ TRUE  -> TRUE
  TRUE :\/ _  -> TRUE
  fm -> fm

-- Simplify a formula one level down
simplify1 :: FreeVars a => Formula a -> Formula a
simplify1 = \case
  fm@(Forall x p) -> if x ∈ fv p then fm else p
  fm@(Exists x p) -> if x ∈ fv p then fm else p
  fm -> psimplify1 fm

-- Simplify a formula recursively
simplify :: FreeVars a => Formula a -> Formula a
simplify = \case
  Not p      -> simplify1 (Not (simplify p))
  p :/\  q   -> simplify1 (simplify p :/\ simplify q)
  p :\/  q   -> simplify1 (simplify p :\/ simplify q)
  Forall x p -> simplify1 (Forall x (simplify p))
  Exists x p -> simplify1 (Exists x (simplify p))
  Atom a     -> Atom a
  TRUE       -> TRUE
  FALSE      -> FALSE

-- Conversion to negation-normal form
nnf :: Formula a -> Formula a
nnf = nnf' . psimplify
  where
    nnf' = \case
      p :/\ q -> nnf' p :/\ nnf' q
      p :\/ q -> nnf' p :\/ nnf' q
      Not (Not p) -> nnf' p
      Not (p :/\ q) -> nnf' (Not p) :\/ nnf' (Not q)
      Not (p :\/ q) -> nnf' (Not p) :/\ nnf' (Not q)
      fm -> fm

-- Conversion to disjunctive normal form, represented as a list-of-lists
purednf :: Ord a => Formula a -> [[Formula a]]
purednf = map Set.toList . Set.toList . purednf'
  where
    purednf' :: Ord a => Formula a -> Set (Set (Formula a))
    purednf' = \case
      p :/\ q -> distrib (purednf' p) (purednf' q)
      p :\/ q -> purednf' p ∪ purednf' q
      fm      -> Set.singleton (Set.singleton fm)

    distrib s1 s2 =
      Set.fromList [xs ∪ ys | xs <- Set.toList s1
                            , ys <- Set.toList s2]

-- Negate a formula without leading to not-chains.
negate :: Formula a -> Formula a
negate (Not p) =     p
negate      p  = Not p

conjoin, disjoin :: [Formula a] -> Formula a

-- Conjoin a list of formulae
conjoin [] = TRUE
conjoin fs = foldr1 (:/\) fs

-- Disjoin a list of formulae
disjoin [] = FALSE
disjoin fs = foldr1 (:\/) fs

conjuncts, disjuncts :: Formula a -> [Formula a]

-- Split a formula into top-level conjuncts
conjuncts = \case
  p :/\ q -> conjuncts p ++ conjuncts q
  fm      -> [fm]

-- Split a formula into top-level disjuncts
disjuncts = \case
  p :\/ q -> disjuncts p ++ disjuncts q
  fm      -> [fm]

-- Takes a list of formulae and minimally existentially quantifies with the given variable
minExists :: FreeVars a => Variable -> [Formula a] -> Formula a
minExists x conjs =
  case partition ((x ∈) . fv) conjs of
    ([], no)  -> conjoin no
    (yes, []) -> Exists x (conjoin yes)
    (yes, no) -> Exists x (conjoin yes) :/\ conjoin no

-- x -> formula -> exists x. f1 \/ exists x. f2 \/ ...
pushquant :: (FreeVars a, Ord a) => Variable -> Formula a -> Formula a
pushquant x p =
  if x ∉ fv p then p else
  let disjs = purednf (nnf p) in
  disjoin $ map (minExists x) disjs

-- Minimize the scope of quantifiers as much as possible
miniscope :: (FreeVars a, Ord a) => Formula a -> Formula a
miniscope = \case
  Not p -> Not (miniscope p)
  p :/\ q -> miniscope p :/\ miniscope q
  p :\/ q -> miniscope p :\/ miniscope q
  Forall x p -> Not (pushquant x (Not (miniscope p)))
  Exists x p -> pushquant x (miniscope p)
  fm -> fm

-- Apply a quantifier elimination procedure only to the existential relevant to x
qelim :: FreeVars a => (Formula a -> Formula a) -> Variable -> Formula a -> Formula a
qelim qfn x p =
  let cjs = conjuncts p in
  case partition ((x ∈) . fv) cjs of
    ([], _) -> p
    (ycjs, ncjs) ->
      let q = qfn (Exists x $ conjoin ycjs) in
      foldr (:/\) q ncjs

-- Generic parameterized quantifier elimination
liftQelim :: (FreeVars a, FreeVars b, Ord a, Ord b)
          => (a -> b) -- thing to do to atoms -- canonicalization or soemthing
          -> (Formula b -> Formula b) -- dnf conversion + maybe extra stuff
          -> (Formula b -> Formula b) -- core quantifier elimination procedure
          -> Formula a -- input formula
          -> Formula b
liftQelim afn nfn qfn fm
  = simplify . qelift . miniscope $ fm
  where
    qelift = \case
      TRUE  -> TRUE
      FALSE -> FALSE
      Atom a -> Atom (afn a)
      Not p -> Not (qelift p)
      p :/\ q -> qelift p :/\ qelift q
      p :\/ q -> qelift p :\/ qelift q
      Forall x p -> Not (qelift (Exists x (Not p)))
      Exists x p ->
        disjoin . map (qelim qfn x) .
          disjuncts . (nfn . qelift) $ p

-- "Clever" negation-normal-form transformation, which incorporates an optimization for
-- "case-splitting" formulae, as well as being parameterized over a "literal modification" function
cnnf :: (Eq a, FreeVars a) => (Formula a -> Formula a) -> Formula a -> Formula a
cnnf lfn = simplify . cnnf' . simplify
  where
    cnnf' = \case
      p :/\ q -> cnnf' p :/\ cnnf' q
      p :\/ q -> cnnf' p :\/ cnnf' q
      Not (Not p) -> cnnf' p
      Not (p :/\ q) -> cnnf' (Not p) :\/ cnnf' (Not q)
      Not ((p :/\ q) :\/ (p' :/\ r)) | p' == negate p -> -- special case optimization
        cnnf' (p :/\ Not q) :\/ cnnf' (p' :/\ Not r)
      Not (p :\/ q) -> cnnf' (Not p) :/\ cnnf' (Not q)
      fm -> lfn fm

-- Computing free variables

class FreeVars a where
  fv :: a -> Set Variable

instance FreeVars Term where
  fv = \case
    k  :* t -> fv t
    t1 :+ t2 -> fv t1 ∪ fv t2
    t1 :- t2 -> fv t1 ∪ fv t2
    C _ -> Set.empty
    V v -> Set.singleton v

instance FreeVars CTerm where
  fv (CT m _) = Map.keysSet m

instance FreeVars Atom where
  fv = \case
    t1 :<  t2 -> fv t1 ∪ fv t2
    t1 :<= t2 -> fv t1 ∪ fv t2
    t1 :== t2 -> fv t1 ∪ fv t2
    t1 :>= t2 -> fv t1 ∪ fv t2
    t1 :>  t2 -> fv t1 ∪ fv t2
    _  :|  t  -> fv t

instance FreeVars CAtom where
  fv = \case
    EqualZero   t -> fv t
    GreaterZero t -> fv t
    Divides _   t -> fv t

instance FreeVars a => FreeVars (Formula a) where
  fv = \case
    Not f      -> fv f
    f1 :/\ f2  -> fv f1 ∪ fv f2
    f1 :\/ f2  -> fv f1 ∪ fv f2
    Forall x f -> fv f ∖ Set.singleton x
    Exists x f -> fv f ∖ Set.singleton x
    Atom a -> fv a
    _ -> Set.empty

infixl 6 .+
infixl 7 .*
infixl 6 .-
infixl 6 :+
infixl 7 :*
infixl 6 :-
infix 4 :<
infix 4 :<=
infix 4 :>=
infix 4 :==
infix 4 :>
infix 4 :|
infixr 3 :/\
infixr 2 :\/
infixr 1 ==>
infixr 0 <=>

deriving instance Show CAtom
deriving instance Show CTerm
deriving instance Show Atom
deriving instance Show Term
deriving instance Show a => Show (Formula a)

deriving instance Eq CAtom
deriving instance Eq CTerm
deriving instance Eq Atom
deriving instance Eq Term
deriving instance Eq a => Eq (Formula a)

deriving instance Ord CAtom
deriving instance Ord CTerm
deriving instance Ord Atom
deriving instance Ord Term
deriving instance Ord a => Ord (Formula a)

deriving instance Functor Formula

instance Applicative Formula where
  pure = return
  (<*>) = ap

instance Monad Formula where
  return = Atom
  (>>=) = flip onAtoms

instance Num Term where
  fromInteger = C

instance IsString Term where
  fromString = V
