module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CanonicalAnticommutationRelationsConsequence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv

@[expose] public section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.canonical_anticommutation_relations_consequence : ∀ (n : ℕ) (R : Type) [Ring R] (τ : Fin n → Fin n → Prop) [DecidableRel τ] (c d L : Fin n → Fin n → R) (p q : Fin n),
    (∀ a b a' b', c a b * c a' b' + c a' b' * c a b = 0) →
    (∀ a b a' b', d a b * d a' b' + d a' b' * d a b = 0) →
    (∀ a b a' b', c a b * d a' b' + d a' b' * c a b = if a = a' ∧ b = b' ∧ τ a b then 1 else 0) →
    (∀ a b, ¬τ a b → c a b = 0) → (∀ a b, ¬τ a b → d a b = 0) →
    (∀ b, τ p b ↔ τ q b) → (∀ a, τ a p ↔ τ a q) →
    (∀ a b a' b', Commute (L a b) (c a' b')) → (∀ a b a' b', Commute (L a b) (d a' b')) →
    (∀ a b, L p q * L a b - L a b * L p q = (if q = a then L p b else 0) - (if b = p then L a q else 0)) →
    Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p))
      ((∑ a, ∑ b, L a b * c a b) + ∑ a, ∑ b, ∑ e, d a e * c b e * c a b) := by
  first | exact @GlobalTheory.CompanionTheory.CliffordCoeff.commute_shifted_dirac | exact GlobalTheory.CompanionTheory.CliffordCoeff.commute_shifted_dirac | (intros; apply GlobalTheory.CompanionTheory.CliffordCoeff.commute_shifted_dirac <;> assumption)
