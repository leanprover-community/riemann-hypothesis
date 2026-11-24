module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresUniqueAe
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

@[expose] public section


theorem _root_.GlobalTheory.T.localization_inverse_mod_f : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (f : B) (P : Ideal B) (Q : Ideal D) (g : D), Q.comap (algebraMap B D) = P → (∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) → ∀ s : B, s ∉ P → ∃ t : Localization.Away g, algebraMap B (Localization.Away g) s * t - 1 ∈ Ideal.span {algebraMap B (Localization.Away g) f} := by
  first | (exact @GlobalTheory.unitsMod_away_of_unique_prime) | (exact GlobalTheory.unitsMod_away_of_unique_prime) | (intros; apply GlobalTheory.unitsMod_away_of_unique_prime <;> assumption)
