module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionElementFrobeniusPowerStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivialStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjWD

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.ConjWD

namespace GlobalTheory.ConjWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_weil_eq_on {g : G E Ω} (hg : g ∈ Dec (F := E) A) (L : IntermediateField E Ω)
    [FiniteDimensional E L] : ∃ τ : Weil h, ∀ x ∈ L, (τ : G E Ω) x = g x := by
  obtain ⟨k, hk⟩ := GlobalTheory.T.decomposition_element_frobenius_power E Ω A w h L inferInstance g hg
  set φ : Weil h := frob h ^ k
  have hφ : ActsAs A (normV w) (φ : G E Ω) k 0 := actsAs_of_deg (by simp [φ])
  have hψ : ((φ : G E Ω) * g) ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem hφ.1 hg
  obtain ⟨ι, hι, hιL⟩ := GlobalTheory.T.inertia_lift_of_residual_trivial E Ω A w h L _ hψ fun x hx hxi => by
    have hx1 : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr (mem_of_isIntegral_int A hxi)
    have hgx : A.valuation (g x) ≤ 1 := val_apply_le_one hg hx1
    have h1 := hφ.2 _ hgx
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (hk x hx hxi)
  refine ⟨φ⁻¹ * ineIncl h ⟨ι, hι⟩, fun x hx => ?_⟩
  show (φ : G E Ω)⁻¹ (ι x) = g x
  rw [hιL x hx, AlgEquiv.mul_apply]
  show ((φ : G E Ω)⁻¹ * (φ : G E Ω)) (g x) = g x
  simp

end GlobalTheory.ConjWD
