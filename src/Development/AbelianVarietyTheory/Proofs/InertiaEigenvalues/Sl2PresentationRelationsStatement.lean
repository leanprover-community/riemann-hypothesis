module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2PresentationRelations
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss

@[expose] public section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_hom_specialLinearGroup_of_relations : ∀ (K : Type) [CommRing K], IsField K → ∀ (M : Type) [Monoid M] (n : K → M) (m : Kˣ → M) (t : M), n 0 = 1 → (∀ a b, n (a + b) = n a * n b) → m 1 = 1 → (∀ a b, m (a * b) = m a * m b) → (∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) → t * t = m (-1) → (∀ s, t * m s = m s⁻¹ * t) → (∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K))) → ∃ ρ : SpecialLinearGroup (Fin 2) K →* M, (∀ z, ρ (nS z) = n z) ∧ (∀ s, ρ (mS s) = m s) ∧ ρ (wS K) = t := by
  first | exact @GlobalTheory.BruhatRep.exists_hom_of_bruhat | exact GlobalTheory.BruhatRep.exists_hom_of_bruhat | (intros; apply GlobalTheory.BruhatRep.exists_hom_of_bruhat <;> assumption)
