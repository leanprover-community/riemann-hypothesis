module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiNormCoord

open Formalism.L2.Pj

variable {R : Type} [CommRing R] [IsDomain R]

theorem valF_eq {D : DegPre R} {χ : D.X} {r : R} (j : PUnit → D.P.L.ι)
    (h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j)
    (e : ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) :
    valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  unfold valF
  rw [dite_eq_left (by exact h)]
  have e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j),
      (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R)))
        ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val
      = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val := by
    intro h'
    rfl
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_
  have e2 : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    simp only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e2]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have n' := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'
  exact n'.symm

theorem exists_unit_valF {D : DegPre R} {χ : D.X} {r : R} (hr : PsiCoord D χ r) (j : PUnit → D.P.L.ι)
    (hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit)) :
    ∃ u : Rˣ, valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) (u * r) := by
  obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
  have h := PsiCoordLocal.generic_le D χ j hj
  obtain ⟨u, hu⟩ := PsiCoordLocal.exists_trans D χ j j₀ hj hj₀ h h₀
  let φ := RingEquiv.ofBijective _ (PsiCoordLocal.toOpen_top_bijective (R := R))
  refine ⟨Units.map φ.symm.toMonoidHom u, valF_eq j h ?_⟩
  have k : DegPre.toOpen (R := R) ⊤ (Units.map φ.symm.toMonoidHom u : Rˣ) = u := φ.apply_symm_apply u.val
  rw [map_mul, map_mul, k, e₀]
  exact (congrArg Units.val hu).symm

theorem norm_unit {S C : Type} [CommRing S] [NormedField C] (f : S →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Sˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Sˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = _ := mul_one _

theorem main : ∀ (p : ℕ) [Fact p.Prime] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra (FractionRing W) (PadicAlgCl p)], (∀ x : FractionRing W, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) → ∀ (D : DegData W (maximalIdeal W)) (y : D.toPre.X), (∃ r, Formalism.L2.Pj.PsiCoord D.toPre y r) ∧ ∀ r, Formalism.L2.Pj.PsiCoord D.toPre y r → ∀ t : ℝ, (GlobalTheory.UnifTorsK.PsiNormAt p D.toPre y t ↔ ‖algebraMap (FractionRing W) (PadicAlgCl p) (algebraMap W _ r)‖ = t) := by
  intro p _ W _ _ _ _ hball D y
  haveI : CharZero W :=
    ((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))).charZero
  have hf : ∀ a : W, ‖((algebraMap (FractionRing W) (PadicAlgCl p)).comp (algebraMap W (FractionRing W))) a‖ ≤ 1 :=
    fun a => (hball _).2 ⟨a, rfl⟩
  refine ⟨((GlobalTheory.PsiCoordLocal.main W D inferInstance y).1).imp fun r h => h.1, fun r hr t => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j₀, hj₀, h₀, e₀⟩ := hr
    have := h j₀ hj₀
    rwa [valF_eq j₀ h₀ e₀] at this
  · intro j hj
    obtain ⟨u, hu⟩ := exists_unit_valF hr j hj
    rw [hu, map_mul, map_mul, norm_mul]
    have := norm_unit _ hf u
    simp only [RingHom.comp_apply] at this
    rw [this, _root_.one_mul, h]

end GlobalTheory.PsiNormCoord
