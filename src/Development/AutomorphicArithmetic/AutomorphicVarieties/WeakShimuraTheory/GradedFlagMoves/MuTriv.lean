module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.CharP.Lemmas
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rt.muTriv :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H : Subgroup Γ) (k : Type) [Field k] [CharP k l]
      (ψ : Γ →* k), IsLocallyConstant ψ → ∀ s ∈ muOf l H, ψ s = 1 := by
  intro l _ Γ _ _ _ H k _ _ ψ hψ s hs
  obtain ⟨-, a, ha⟩ := hs
  have hcl : IsClosed ((ψ.ker : Subgroup Γ) : Set Γ) := by
    have e : ((ψ.ker : Subgroup Γ) : Set Γ) = {x | ψ x = 1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [e]
    exact hψ.isClosed_fiber 1
  have hle : ⁅H, H⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul]
    calc ψ g₁ * ψ g₂ * ψ g₁⁻¹ * ψ g₂⁻¹ = ψ (g₁ * g₁⁻¹) * ψ (g₂ * g₂⁻¹) := by
          rw [map_mul, map_mul]; ring
      _ = 1 := by simp
  have hm := Subgroup.topologicalClosure_minimal _ hle hcl ha
  rw [MonoidHom.mem_ker, map_pow] at hm
  have h0 : (ψ s - 1) ^ l ^ a = 0 := by
    rw [sub_pow_char_pow, hm, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h0)
