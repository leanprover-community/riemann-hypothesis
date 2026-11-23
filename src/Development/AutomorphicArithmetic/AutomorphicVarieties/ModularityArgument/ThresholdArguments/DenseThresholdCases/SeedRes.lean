module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChainMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
namespace UpperTheory.V.Ws.Chn
variable {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] {Φ : Fr O Γ} {a : O →+* k}
variable {ι Γ R : Type} [Group Γ] [CommRing R] {P P' : PD ι Γ R}
variable {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R}
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}
theorem seed_res_alt (T : Tower D) (𝔞 : Amb l) {ι : PadicAlgCl l ≃+* ℂ} {c₁ : Coef l} {h : c.O ≤ c₁.O}
    {Q : PD T.ι (G T.F Ω) c₁.O} (hQ : T.SeedPairAlt ι h Q) : (T.fr ∅).IsRes (𝔞.red c) (Q.map (𝔞.red c₁)) := by
  have h1 : (T.fr ∅).IsRes ((residue c₁.O).comp (inc h)) (Q.map (residue c₁.O)) := by
    refine ⟨pair_map hQ.pair _, hQ.res, fun i j n => ?_⟩
    have h2 := (hQ.cont i j 1).comp (Ideal.Quotient.lift (maximalIdeal c₁.O ^ 1) (residue c₁.O)
      fun x hx => (residue_eq_zero_iff x).2 (by rwa [pow_one] at hx))
    exact h2.comp (Ideal.Quotient.mk ((⊥ : Ideal (ResidueField c₁.O)) ^ n))
  have h2 := (chainMap (T.fr ∅) _ (𝔞.j c₁) _).1.2 h1
  have e1 : (𝔞.j c₁).comp ((residue c₁.O).comp (inc h)) = 𝔞.red c :=
    RingHom.ext fun x => congrArg (residue 𝔞.V) (𝔞.compat c c₁ h x)
  rw [e1] at h2
  exact h2
end Gal
end UpperTheory.V.Ws.Chn
end
