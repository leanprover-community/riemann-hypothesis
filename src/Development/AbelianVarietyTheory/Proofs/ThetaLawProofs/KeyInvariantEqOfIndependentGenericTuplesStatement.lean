module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantEqOfIndependentGenericTuples
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.keyInvariant_eq_of_independent_generic_tuples : Out.Laws → ∀ (k K : Type) [Field k] [CharZero k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T T' : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s s' : Fin x'.P.g → RR x' n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k (Sum.elim T T') → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → (∀ i, Coords x' b' (fun j => T' (i, j)) (s' i).f) → KaVal x' n l l' al s κ → KaVal x' n l l' al s' κ' → κ = κ' := by
  first | exact @GlobalTheory.KeyGeneric.kaVal_eq_of_generic | exact GlobalTheory.KeyGeneric.kaVal_eq_of_generic | (intros; apply GlobalTheory.KeyGeneric.kaVal_eq_of_generic <;> assumption)
