module

public import Formalism.RealPlaceAnalysis.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.WordWeight

theorem step {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℝ) (v : V)
    (hv : IsWeight E ν v) (a b : Fin n) :
    IsWeight E (ν + root a b) (E a b v) := by
  intro c
  have h := hE c c a b
  have h2 : E c c (E a b v) = E a b (E c c v) +
      ((if c = a then E c b else 0) - (if b = c then E a c else 0)) v := by
    rw [← h]; simp
  rw [h2, hv c, map_smul]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hca : c = a <;> by_cases hbc : b = c
  · subst hca; subst hbc; simp
  · subst hca
    have : ¬ c = b := fun h => hbc h.symm
    simp [this, hbc]
    rw [add_smul, one_smul]
    rfl
  · subst hbc
    simp [hca]
    rw [add_smul, neg_smul, one_smul]
    rfl
  · have : ¬ c = b := fun h => hbc h.symm
    simp [hca, this, hbc]

theorem word {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    ∀ (l : List (Fin n × Fin n)) (μ : Fin n → ℝ) (w : V), IsWeight E μ w →
    IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum)
      ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  intro l μ w hw
  induction l with
  | nil => simpa using hw
  | cons p l ih =>
    have := step E hE _ _ ih p.1 p.2
    simp only [List.map_cons, List.sum_cons, List.prod_cons, mul_apply_eq_comp]
    convert this using 1
    abel

end GlobalTheory.WordWeight

theorem GlobalTheory.wordWeight : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (μ : Fin n → ℝ) (w : V), IsWeight E μ w → ∀ l : List (Fin n × Fin n), IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum) ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  intro n V _ _ E hE μ w hw l
  exact GlobalTheory.WordWeight.word E hE l μ w hw
