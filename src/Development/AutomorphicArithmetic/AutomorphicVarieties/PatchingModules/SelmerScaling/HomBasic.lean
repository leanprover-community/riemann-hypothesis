module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.homBasic :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0), Function.Surjective h.p₀ ∧ Continuous h.p₀ ∧ (∀ g, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g)) ∧ (∀ v g, h.p₀ (G.φ v g) = G0.φ v g) ∧ (∀ w, ∀ g ∈ G.frame.Iu w, h.p₀ g ∈ G0.frame.Iu w) ∧ ∀ (O R : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] (g : G.G₀), G0.frame.eps O R (h.p₀ g) = G.frame.eps O R g := by
  intro l _ L G G0 h
  refine ⟨fun g => ?_, (h.cont.comp continuous_subtype_val).subtype_mk _, fun g => Subtype.ext ?_,
    fun v g => Subtype.ext (h.φ v g), ?_, fun O R _ _ _ _ g => ?_⟩
  · obtain ⟨a, ha⟩ := h.surj g
    exact ⟨⟨a, by rw [MonoidHom.mem_ker, ← h.η, ha]; exact g.2⟩, Subtype.ext ha⟩
  · change h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c]
  · rintro w _ ⟨j, hj, rfl⟩
    exact ⟨j, hj, Subtype.ext (h.φu w j).symm⟩
  · change Units.map _ (G0.ε (h.p g)) = Units.map _ (G.ε g)
    rw [h.ε]
