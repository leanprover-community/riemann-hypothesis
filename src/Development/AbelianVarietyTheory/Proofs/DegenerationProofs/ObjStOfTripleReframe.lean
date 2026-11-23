module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeUniformisationOfPrimTheta
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsOfDouble
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertDataOfIsoCube
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem int_eq_of_exp_div_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  apply GlobalTheory.ExpUniqFamily.int_eq_of_exp <;> assumption

theorem objSt_of_triple_reframe : Laws → TripleSt → ReframeSt → ObjSt := by
  intro laws hT hR E _ _ _ H D La _ _ EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨Q, oa, L₀, u₀, hg, hiso, hdet, ht₁, ht₂, hker, hact, hW⟩ :=
    hT E H D La EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨u, Hm, χ, Ef, F, hAH, hE, hF⟩ := hR Q L₀ g u₀ hg ht₁ ht₂
  have hΛ : ∀ a, F (P a) ∈ u.Λ := fun a => (u.ker _).1 ((hF _).trans ((hker _).2 ⟨a, rfl⟩))
  have hsur : ∀ z ∈ u.Λ, ∃ a, z = F (P a) := fun z hz => by
    obtain ⟨w, rfl⟩ := F.surjective z
    obtain ⟨a, ha⟩ := (hker w).1 ((hF w).symm.trans ((u.ker _).2 hz))
    exact ⟨a, by rw [ha]⟩
  have hW' : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • F (P a))) (u.ex ((k : ℂ)⁻¹ • F (P b))) (unitOn c) := fun k a b c hk hc => by
    rw [← map_smul F, ← map_smul F, hF, hF]
    exact hW k a b c hk hc
  have hEf : ∀ a b, Ef ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩ = EF a b := fun a b => int_eq_of_exp_div_eq fun k hk => by
    have w₁ := PeriodPoint.weilIs_of_isAH laws Q rfl u hAH Ef hE k ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w₂ := hW' k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    exact congrArg Units.val
      (PrimUnif.unitOn_inj' (CommutatorPairing.weilIs_unique laws.globalFns Q.isAb Q.isLB w₁ w₂))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (F fun k => ty k (a : E) * z k) = u.ex (F z) ≫ oa.act a := fun a z => by
    rw [hF, hF, hact]
  let d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi fun k => ty k (H.w0 : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) k
  let G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ) := F.toLinearMap ∘ₗ d ∘ₗ F.symm.toLinearMap
  have hG : ∀ z, G (F z) = F fun k => ty k (H.w0 : E) * z k := fun z => by
    change F (d (F.symm (F z))) = _
    rw [F.symm_apply_apply]
    rfl
  have hGP : ∀ a, G (F (P a)) = F (P (H.w0 • a)) := fun a => by
    rw [hG]
    congr 1
    funext k
    exact (h4 _ _ _).symm
  have hGΛ : ∀ l ∈ u.Λ, G l ∈ u.Λ := fun l hl => by
    obtain ⟨a, rfl⟩ := hsur l hl
    rw [hGP]
    exact hΛ _
  have hGex : ∀ z, u.ex (G z) = u.ex z ≫ oa.act H.w0 := fun z => by
    obtain ⟨w, rfl⟩ := F.surjective z
    rw [hG, hact']
  have hχ := (@GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube GlobalTheory.valAt'_rules
    (GlobalTheory.holFamily_lift GlobalTheory.valAt'_rules) Q Q.isAb.comm u Hm χ Ef
    ⟨hAH.1, hAH.2.2.1, hE, hAH.2.2.2⟩ (oa.act H.w0) G hGΛ hGex hiso).2
  refine ⟨Q, oa, u, Hm, χ, F, hΛ, hiso, hdet, hAH, hsur, fun a b => ?_, fun a => ?_, hact', hW'⟩
  · rw [← hEf]
    exact (hE ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩).symm
  · rw [hχ, ← hEf]
    congr 2
    exact Subtype.ext (hGP a)

end GlobalTheory.Ex.Arch
end
