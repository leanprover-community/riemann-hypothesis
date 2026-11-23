module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.TnOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

namespace UpperTheory.V.Cu2

namespace AlgType

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime]

private theorem isAlgPos_mul {χ χ' : HChar K} {n n' : (K →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar K} {n : (K →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

def Good (art : Ideles K →* Gab K Ω) (ι : Qbar l ≃+* ℂ) (t : (K →+* ℂ) → ℤ) (ψ : G K Ω →* (Qbar l)ˣ) : Prop :=
  ∃ Y : HChar K, IsAlgPos Y t ∧ IsLAdicOf art ι Y t ψ

theorem good_cong {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t t' : (K →+* ℂ) → ℤ}
    {ψ ψ' : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) (ht : t = t') (hψ : ψ = ψ') : Good art ι t' ψ' := by
  subst ht hψ
  exact h

theorem good_mul {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t t' : (K →+* ℂ) → ℤ}
    {ψ ψ' : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) (h' : Good art ι t' ψ') : Good art ι (t + t') (ψ * ψ') := by
  obtain ⟨Y, h1, h2⟩ := h
  obtain ⟨Y', h1', h2'⟩ := h'
  exact ⟨Y * Y', isAlgPos_mul h1 h1', h2.mul h2'⟩

theorem good_one {art : Ideles K →* Gab K Ω} {ι : Qbar l ≃+* ℂ} {t : (K →+* ℂ) → ℤ}
    {ψ : G K Ω →* (Qbar l)ˣ} (h : Good art ι t ψ) : Good art ι 0 1 := by
  obtain ⟨Y, h1, h2⟩ := h
  exact good_cong ⟨Y * Y⁻¹, isAlgPos_mul h1 (isAlgPos_inv h1), h2.mul h2.inv⟩ (add_neg_cancel t) (mul_inv_cancel ψ)

theorem good_cyc {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) :
    Good art ι (fun _ => 1) (cycBar K Ω l) := by
  have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos K 1
  obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
  have e : μ = cycBar K Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at e
  subst e
  exact good_cong ⟨_, h, hL⟩ (funext fun _ => Nat.cast_one) rfl

end AlgType


end UpperTheory.V.Cu2

end
