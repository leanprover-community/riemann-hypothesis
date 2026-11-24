module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBumpStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerMulTorusIteratedFactorisation
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.BumpShintani

theorem pInf_tl {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) :
    GeneralLinearGroup.map (pInf E) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, _, rfl⟩ := hx
  simp

theorem loc_tl {E : Type} [Field E] [NumberField E] {a : ℕ} (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ)) (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ l.support) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 := by
  unfold GlobalTheory.JSW.tl
  rw [map_list_prod]
  apply List.prod_eq_one
  intro x hx
  simp only [List.map_map, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have hne : v ≠ w := fun h => hv (h ▸ (Finset.mem_toList.1 hw))
  simp only [Function.comp_apply, _root_.GlobalTheory.JSW.MirPatch.Decomp.map_comp_eq, pFin_finGL]
  exact pLoc_locGL_of_ne hne _

theorem exists_bump_shintani : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ ∀ (π : CuspSub E (m + 1)) (α : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ w ∉ S, ∀ k ∈ KGL w (n := (m + 1)), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) ∧ ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w) := by
  intro E _ _ _ m S hcond
  obtain ⟨b, hb1, hbN, hbC, hbU, hbS⟩ := _root_.GlobalTheory.WhitBump.exists_bump E m S
  refine ⟨b, hb1, hbN, hbC, ?_⟩
  intro π α hSat
  obtain ⟨φ, hφV, hφK, hφx⟩ := _root_.GlobalTheory.JSW.NzSph.exists_sph_whit_ne_zero E m S hcond π α hSat
  obtain ⟨F, hFV, hFb, hFU, hFinv, hFeig⟩ := GlobalTheory.T.kirillov_semilocal_smooth_bump E m S b hbN hbC hbU hbS π φ hφV hφx
  refine ⟨F, hFV, hFU, ?_, ?_⟩
  · intro w hw k hk g
    refine hFinv _ (pInf_finGL _) ?_ ?_ g
    · intro w' hw'
      have hne : w' ≠ w := fun h => hw (h ▸ hw')
      rw [_root_.GlobalTheory.JSW.MirPatch.Decomp.map_comp_eq, pFin_finGL]
      exact pLoc_locGL_of_ne hne _
    · intro g'
      exact congrArg (fun ψ : Sm E (m + 1) => ψ.1 g') (hφK w hw k hk)
  · intro ϖ hϖ l hl p hp
    have hC := _root_.GlobalTheory.JSW.whit_mul_tl E (m + 1) S hcond π α hSat φ hφV hφK ϖ hϖ l hl
    have hS : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (GlobalTheory.JSW.tl ϖ l) = 1 :=
      fun w hw => loc_tl ϖ l w (fun h => hl w h hw)
    rw [hFeig _ _ (pInf_tl ϖ l) hS hC p hp.1, hFb p hp, mul_comm]

end GlobalTheory.JSW.BumpShintani
