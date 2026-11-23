module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FbarExistsComplexAutCompEqStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyResidueFieldUnitBallEquiv
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section
namespace GlobalTheory.TeichPlace

theorem exists_place_isTeich : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  intro g _ t ht
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex g
  obtain ⟨κ₀⟩ := GlobalTheory.HeightCounting.nonempty_residueField_unitBall_equiv ι
  obtain ⟨t₀, ht₀, hinj₀⟩ := GlobalTheory.T.exists_teichmuller_reindex_complexPlace g (GlobalTheory.HeightCounting.unitBall ι) κ₀ t ht
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.fbar_exists_complexAut_comp_eq g t t₀ ht hinj₀
  let A : ValuationSubring ℂ := (GlobalTheory.HeightCounting.unitBall ι).comap (σ.symm : ℂ →+* ℂ)
  have hmem : ∀ z : ℂ, z ∈ A ↔ σ.symm z ∈ GlobalTheory.HeightCounting.unitBall ι := fun z => ValuationSubring.mem_comap
  let e : A ≃+* GlobalTheory.HeightCounting.unitBall ι :=
    { toFun := fun a => ⟨σ.symm a, (hmem a).1 a.2⟩
      invFun := fun b => ⟨σ b, (hmem _).2 (by simpa using b.2)⟩
      left_inv := fun a => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  refine ⟨A, (IsLocalRing.ResidueField.mapEquiv e).trans κ₀, fun x => ?_⟩
  have hx : σ.symm (t x) = t₀ x := by rw [← hσ x, RingEquiv.symm_apply_apply]
  obtain ⟨h₀, e₀⟩ := ht₀ x
  refine ⟨(hmem _).2 (hx ▸ h₀), ?_⟩
  refine Eq.trans ?_ e₀
  change κ₀ (IsLocalRing.ResidueField.map (e : A →+* GlobalTheory.HeightCounting.unitBall ι) (IsLocalRing.residue A _)) = _
  rw [IsLocalRing.ResidueField.map_residue]
  congr 2
  exact Subtype.ext hx

end GlobalTheory.TeichPlace
