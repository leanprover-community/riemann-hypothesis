module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.GlCongr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem twKer_mono (ρ : Representation ℂ G V) {N₁ N₂ : Subgroup G} (θ₁ : N₁ →* ℂˣ) (θ₂ : N₂ →* ℂˣ) (hN : N₁ ≤ N₂)
    (hθ : ∀ u : N₁, θ₂ ⟨u, hN u.2⟩ = θ₁ u) : twKer ρ N₁ θ₁ ≤ twKer ρ N₂ θ₂ := by
  apply Submodule.span_mono
  rintro w ⟨n, v, rfl⟩
  exact ⟨⟨n, hN n.2⟩, v, by rw [hθ]⟩

theorem diag_real {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : ∀ v w, B w v = starRingEnd ℂ (B v w)) (v : V) :
    (B v v).im = 0 := Complex.conj_eq_iff_im.mp (hB v v).symm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Chars

theorem whitCharFrom_eq (ψ : AddChar k Circle) {N ℓ a b : ℕ} (u : unipB k (Fin N))
    (hu : (u : GL (Fin N) k) ∈ colFix k N ℓ) (hab : a ≤ b) (hb : b < ℓ) :
    whitCharFrom k ψ N a u = whitCharFrom k ψ N b u := by
  have hfix := (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).mp hu
  unfold whitCharFrom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 2
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, hab.trans hp.2⟩
  · intro p hp hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hp hnot
    have hlt : (p.1 : ℕ) < b := hnot hp.1
    have h2 : (p.2 : ℕ) < ℓ := by omega
    have hq := hfix p.1 p.2 h2
    rw [Matrix.one_apply_ne] at hq
    · exact hq
    · intro h
      rw [h] at hp
      omega

theorem derUnip_anti {N a b : ℕ} (hab : b ≤ a) : derUnip k N a ≤ derUnip k N b :=
  inf_le_inf_left _ (GlobalTheory.CompanionTheory.BZMirStep.colFix_anti hab)

theorem twKer_derUnip_le (ψ : AddChar k Circle) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) {a b x y : ℕ} (hab : b ≤ a) (hx : x < a) (hy : y < a) :
    twKer π (derUnip k N a) ((whitCharFrom k ψ N x).comp (Subgroup.inclusion (derUnip_le_unipB k N a))) ≤
      twKer π (derUnip k N b) ((whitCharFrom k ψ N y).comp (Subgroup.inclusion (derUnip_le_unipB k N b))) := by
  apply twKer_mono π _ _ (derUnip_anti hab)
  intro u
  have hc : (u : GL (Fin N) k) ∈ colFix k N a := (Subgroup.mem_inf.mp u.2).2
  simp only [MonoidHom.comp_apply]
  rcases le_total x y with h | h
  · exact (whitCharFrom_eq ψ _ hc h hy).symm
  · exact whitCharFrom_eq ψ _ hc h hx

theorem lvlChar_def (ψ : AddChar k Circle) (N n : ℕ) :
    lvlChar k ψ N n = (whitCharFrom k ψ N (n - 1)).comp (Subgroup.inclusion (derUnip_le_unipB k N n)) := rfl

theorem derChar_def (ψ : AddChar k Circle) (N n : ℕ) :
    derChar k ψ N n = (whitCharFrom k ψ N n).comp (Subgroup.inclusion (derUnip_le_unipB k N n)) := rfl

theorem colFix_self {N : ℕ} (g : GL (Fin N) k) (hg : g ∈ colFix k N N) : g = 1 := by
  rw [GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff] at hg
  ext i j
  exact hg i j j.2

theorem twKer_derUnip_self (ψ : AddChar k Circle) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (θ : derUnip k N N →* ℂˣ) : twKer π (derUnip k N N) θ = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro _ ⟨u, v, rfl⟩
  have h1 : u = 1 := Subtype.ext (colFix_self _ u.2.2)
  subst h1
  simp

theorem unipB_le_colFix_one (N : ℕ) : unipB k (Fin N) ≤ colFix k N 1 := by
  intro g hg
  rw [GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff]
  rw [mem_unipB] at hg
  intro i j hj
  rcases eq_or_ne i j with rfl | hij
  · rw [hg.2, Matrix.one_apply_eq]
  · rw [hg.1 i j (lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr (by omega)) (Ne.symm hij)), Matrix.one_apply_ne hij]

end Chars

end PositivityTheory.RgUd.Form.U.Asm
