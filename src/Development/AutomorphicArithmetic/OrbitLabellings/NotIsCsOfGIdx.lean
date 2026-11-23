module

public import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions

namespace Formalism.MainNotions.G

theorem frobSet_ne' (D : D7) {p : ℕ} (hp : p.Prime) : ∃ g, g ∈ frobSet D p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have : IsGaloisGroup (D.host.E ≃ₐ[ℚ] D.host.E) ℤ (𝓞 D.host.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  obtain ⟨P, hP, hlo⟩ := (inferInstance : Nonempty (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)))
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)}) (by simpa using hpZ.ne_zero) P
  have : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (D.host.E ≃ₐ[ℚ] D.host.E) P
  exact ⟨_, P, hP, hlo, σ, hσ, rfl⟩

theorem hEv_of_hNeZero {D : D7} {p : ℕ} (hp : p.Prime) (hN : HNeZero D.host p) : HEv D p := by
  obtain ⟨P, hP', hL, σ, hσ, hg⟩ := Classical.epsilon_spec (frobSet_ne' D hp)
  have h1 := @hN P hP' hL σ hσ
  rw [hg] at h1
  exact h1

end Formalism.MainNotions.G

end
