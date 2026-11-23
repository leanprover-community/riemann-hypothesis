module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.PAdicHodge.LocalBridge
public import GroundTheory.PAdicHodge.NormalizedTraceTower
public import GroundTheory.PAdicHodge.SenTateCharTower
import GroundTheory.LocalFields.PadicLogSeries
public import GroundTheory.PAdicHodge.BCrisEigenChar
import GroundTheory.PAdicHodge.BCrisEigenFrob
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.PAdicHodge.AInfGalois
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

open GroundTheory.LocalField GroundTheory.PAdicHodge GroundTheory.PAdicHodge.EigenWitt GroundTheory.PAdicHodge.EigenChar

theorem exists_pow_eigenvector_of_unramified_units {l : ℕ} [Fact l.Prime]
    (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E]
    (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ) (hψ : Continuous ψ)
    (hI : ∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) :
    ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
      σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  have := isSepClosure_padicAlgCl (p := l) (L := E)
  obtain ⟨σ₀, hσ₀⟩ := unramifiedDegree_surjective (K := E) (Ω := PadicAlgCl l)
    (Multiplicative.ofAdd 1)
  set w : ℤ_[l]ˣ := ψ σ₀ with hwdef
  obtain ⟨f, hf, hq⟩ := exists_card_residueField_eq_pow (p := l) (L := E)
  obtain ⟨b, hb, hbσ⟩ := exists_unit_aInf_eigen (K := E) w
  set cA := wittToAInf (b : WittVector l (Fpbar l)) with hcA
  have hcu : IsUnit cA := b.isUnit.map _
  set θ := WittVector.fontaineTheta (normInteger ℂ_[l]) l
  set xc : ℂ_[l] := ((θ cA : normInteger ℂ_[l]) : ℂ_[l]) with hxcdef
  have hxc : xc ≠ 0 := by
    have h1 : θ cA ≠ 0 := (hcu.map θ).ne_zero
    exact fun h => h1 (Subtype.ext h)
  choose z hz using hbσ
  have hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[l] ℂ_[l] (z σ) * xc := fun σ => by
    rw [hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul,
      fontaineTheta_padicIntToWitt]
  have hz₀ : (z σ₀ : ℚ_[l]) = ((w : ℤ_[l]) : ℚ_[l]) ^ f := by
    have h1 := gal_smul_twist_of_degree_one hb hq hσ₀
    rw [← hcA, hz σ₀] at h1
    have h2 := hcu.mul_left_inj.1 h1
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[l]) : ℂ_[l])) h2
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    rw [← PadicInt.coe_pow]
    exact algebraMap_padic_cp_injective h3
  have hzI : ∀ σ, unramifiedDegree E (PadicAlgCl l) σ = 1 → (z σ : ℚ_[l]) = 1 := fun σ hσ => by
    have h1 := gal_smul_twist_of_inertia (b : WittVector l (Fpbar l)) hσ
    rw [← hcA, hz σ] at h1
    have h2 : IsPerfectoidField.padicIntToWitt l (z σ) * cA =
        IsPerfectoidField.padicIntToWitt l 1 * cA := by
      rw [h1, map_one, one_mul]
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[l]) : ℂ_[l])) (hcu.mul_left_inj.1 h2)
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    have := algebraMap_padic_cp_injective h3
    rw [this, PadicInt.coe_one]
  obtain ⟨χ, hχc, hχ⟩ := exists_eigenChar hxc (fun σ => ⟨_, hxcσ σ⟩)
  have hχeq : ∀ σ, ((χ σ : ℚ_[l]ˣ) : ℚ_[l]) = (z σ : ℚ_[l]) := fun σ =>
    eq_of_mul_eq hxc ((hχ σ).symm.trans (hxcσ σ))
  have hψne : ∀ σ, ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) ≠ 0 := fun σ => by
    intro h
    exact (ψ σ).ne_zero (Subtype.ext (h.trans PadicInt.coe_zero.symm))
  let ρC : Gal(PadicAlgCl l/E) →* ℂ_[l] :=
    { toFun := fun σ => algebraMap ℚ_[l] ℂ_[l]
        ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * ((χ σ⁻¹ : ℚ_[l]ˣ) : ℚ_[l]))
      map_one' := by simp
      map_mul' := fun a c => by
        simp only [mul_inv_rev, map_mul, Units.val_mul, PadicInt.coe_mul, mul_pow]
        ring }
  have hρC : Continuous ρC := by
    have hc1 : Continuous fun σ : Gal(PadicAlgCl l/E) => (((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
      have hu : Continuous fun σ : Gal(PadicAlgCl l/E) => ((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) :=
        (Units.continuous_val (M := ℤ_[l])).comp hψ
      exact (continuous_subtype_val : Continuous (fun y : ℤ_[l] => (y : ℚ_[l]))).comp hu
    have hc2 : Continuous fun σ : Gal(PadicAlgCl l/E) => ((χ σ⁻¹ : ℚ_[l]ˣ) : ℚ_[l]) :=
      Units.continuous_val.comp (hχc.comp continuous_inv)
    exact isometry_algebraMap_padic_cp.continuous.comp ((hc1.pow f).mul hc2)
  have hρval : ∀ σ, ρC σ = algebraMap ℚ_[l] ℂ_[l]
      ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * (z σ : ℚ_[l])⁻¹) := fun σ => by
    change algebraMap ℚ_[l] ℂ_[l] _ = _
    rw [map_inv, Units.val_inv_eq_inv_val, hχeq]
  have hall := eq_one_of_degree_one ρC hρC hσ₀
    (by rw [hρval, hz₀, ← hwdef, mul_inv_cancel₀ (pow_ne_zero _ (hψne σ₀)), map_one])
    (fun σ hσ => by rw [hρval, hzI σ hσ, hI σ hσ, Units.val_one, PadicInt.coe_one, one_pow, inv_one,
      mul_one, map_one])
  refine ⟨f, hf, xc, hxc, fun σ => ?_⟩
  have h1 : (((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f * (z σ : ℚ_[l])⁻¹ = 1 :=
    algebraMap_padic_cp_injective (by rw [map_one, ← hρval]; exact hall σ)
  have hz0 : (z σ : ℚ_[l]) ≠ 0 := by
    intro h
    rw [h, inv_zero, mul_zero] at h1
    exact zero_ne_one h1
  rw [hxcσ σ, (mul_inv_eq_one₀ hz0).1 h1]

end GlobalTheory.CompanionTheory.LTPer
