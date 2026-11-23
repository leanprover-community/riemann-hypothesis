module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.KS (rsT)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecAff

theorem rsT_eq_rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (s : Γ(X, U)) : rsT s V = rs h s :=
  GlobalTheory.KS.rsT_of_le h s

theorem sec_extend_basicOpen : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (M : LB X), M.IsLB → ∀ (f : Γ(X, ⊤)) (t : ∀ c, Γ(X, M.U c ⊓ X.basicOpen f)), (∀ c c', rsT (t c) (M.U c ⊓ M.U c' ⊓ X.basicOpen f) = rsT (M.g c c').val (M.U c ⊓ M.U c' ⊓ X.basicOpen f) * rsT (t c') (M.U c ⊓ M.U c' ⊓ X.basicOpen f)) → ∃ (N : ℕ) (s : LB.Sec M), ∀ c, rsT (s.f c) (M.U c ⊓ X.basicOpen f) = rsT f (M.U c ⊓ X.basicOpen f) ^ N * t c := by
  intro X _ _ M hM f t ht
  let φ := (X.basicOpen f).ι
  have hφ : φ.opensRange = X.basicOpen f := Scheme.Opens.opensRange_ι _
  have hr : ∀ x, φ x ∈ X.basicOpen f := by
    intro x
    have hx : φ x ∈ φ.opensRange := ⟨x, rfl⟩
    rwa [hφ] at hx
  have hc : ∀ c, φ ⁻¹ᵁ M.U c ≤ φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) := fun c x hx => ⟨hx, hr x⟩
  let t' : ∀ c, Γ(↑(X.basicOpen f), φ ⁻¹ᵁ M.U c) := fun c => pa φ (hc c) (t c)
  have ht' : ∀ i j, rs (inf_le_left : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U i) (t' i) =
      pa φ (le_pre_inf (inf_le_left.trans (le_refl (φ ⁻¹ᵁ M.U i)))
        (inf_le_right.trans (le_refl (φ ⁻¹ᵁ M.U j))))
        (M.g i j : Γ(X, M.U i ⊓ M.U j)) *
        rs (inf_le_right : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ M.U j) (t' j) := by
    intro i j
    have e : φ ⁻¹ᵁ M.U i ⊓ φ ⁻¹ᵁ M.U j ≤ φ ⁻¹ᵁ (M.U i ⊓ M.U j ⊓ X.basicOpen f) :=
      fun x hx => ⟨⟨hx.1, hx.2⟩, hr x⟩
    have h1 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_left
    have h2 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U i ⊓ M.U j := inf_le_left
    have h3 : M.U i ⊓ M.U j ⊓ X.basicOpen f ≤ M.U j ⊓ X.basicOpen f :=
      inf_le_inf_right _ inf_le_right
    have := ht i j
    rw [rsT_eq_rs h1, rsT_eq_rs h2, rsT_eq_rs h3] at this
    have := congrArg (pa φ e) this
    rw [map_mul, pa_rs, pa_rs, pa_rs] at this
    simp only [t']
    rw [rs_pa, rs_pa]
    exact this
  obtain ⟨N, s, hs⟩ := sec_extend φ f hφ M hM (fun c => φ ⁻¹ᵁ M.U c) (fun c => le_rfl)
    (fun c => le_rfl) t' ht'
  refine ⟨N, s, fun c => ?_⟩
  have hU : M.U c ⊓ X.basicOpen f ≤ φ.opensRange := by rw [hφ]; exact inf_le_right
  apply (pa_bijective φ (le_refl (φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f))) le_rfl hU).1
  have hV : φ ⁻¹ᵁ (M.U c ⊓ X.basicOpen f) ≤ φ ⁻¹ᵁ M.U c := fun x hx => hx.1
  have := congrArg (rs hV) (hs c)
  rw [rs_pa, map_mul, map_pow, rs_pa] at this
  simp only [t'] at this
  rw [rs_pa] at this
  rw [rsT_eq_rs inf_le_left, rsT_eq_rs le_top, map_mul, map_pow, pa_rs, pa_rs, this]

end GlobalTheory.SecAff
