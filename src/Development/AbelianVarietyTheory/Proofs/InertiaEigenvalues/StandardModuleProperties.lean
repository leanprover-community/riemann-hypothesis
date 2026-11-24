module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.LocGL.IrrProdL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_eq_of_isL {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {𝔪 : Multiset (Segment k)} (h : IsL 𝔪 π) : (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, ⟨Δ, ⟨rfl, -⟩, hΔ⟩, -⟩ := h
  rw [← hd, Multiset.map_map]
  exact Finset.sum_congr rfl fun i _ => (hΔ i).deg_eq

theorem isL_add [CharZero k] (H : GlobalTheory.Published.LanglandsMultisegments) {𝔪 𝔫 : Multiset (Segment k)} (x t y : IrrGL (k := k))
    (hx : IsL 𝔪 x.rep) (ht : IsL 𝔫 t.rep) (hy : IsL (𝔪 + 𝔫) y.rep)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (x.1 + t.1)) k) V)
    (hπ : π.IsIrreducible) (φ : π.Equiv (prod₂ x.rep t.rep)) : IsL (𝔪 + 𝔫) π := by
  have e : y.1 = x.1 + t.1 := by
    rw [← deg_eq_of_isL hy, ← deg_eq_of_isL hx, ← deg_eq_of_isL ht, Multiset.map_add (f := _), Multiset.sum_add]
  obtain ⟨n, c⟩ := y
  dsimp only at e
  subst e
  have hd : ∑ a, (![x, t] a).1 = x.1 + t.1 := Fin.sum_univ_two _
  have hs := (H k).2 𝔪 𝔫 ![x, t] ⟨x.1 + t.1, c⟩ hd hx ht hy
  obtain ⟨ψ⟩ := nonempty_prod₂_equiv_prodIrr_pair x t hd
  let χ := φ.trans ψ
  have hs' := hs.trans (IsSubquotient.of_surjective χ.toIntertwiningMap χ.toLinearEquiv.surjective)
  obtain ⟨ω⟩ := IsSubquotient.nonempty_equiv hs' hy.irr_smooth.1 hπ
  exact hy.of_equiv ω.symm

private theorem isL_add_of_equiv [CharZero k] (H : GlobalTheory.Published.LanglandsMultisegments)
    {𝔪 𝔫 : Multiset (Segment k)} (x y : IrrGL (k := k))
    {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GL (Fin n) k) W) (hτs : IsSmooth τ) (hτi : τ.IsIrreducible)
    (hx : IsL 𝔪 x.rep) (hτ : IsL 𝔫 τ) (hy : IsL (𝔪 + 𝔫) y.rep)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (x.1 + n)) k) V)
    (hπ : π.IsIrreducible) (χ : π.Equiv (prod₂ x.rep τ)) : IsL (𝔪 + 𝔫) π := by
  let e := IrrGL.equivOf τ hτs hτi
  exact isL_add H x (IrrGL.of τ hτs hτi) y hx (hτ.of_equiv e) hy π hπ
    (χ.trans (prod₂Equiv (Representation.Equiv.refl x.rep) e))

theorem isL_sum_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], GlobalTheory.Published.LanglandsMultisegments →
    ∀ (P : Segment k → Prop), (∀ 𝔫 : Multiset (Segment k), (∀ Δ ∈ 𝔫, P Δ) → ∃ y : IrrGL (k := k), IsL 𝔫 y.rep) →
    ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (𝔪 : Fin h → Multiset (Segment k)),
      (∀ j, IsL (𝔪 j) (x j).rep) → (∀ j, ∀ Δ ∈ 𝔪 j, P Δ) →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible →
        Nonempty (π.Equiv (prodIrr x hd)) → IsL (∑ j, 𝔪 j) π := by
  intro k _ _ _ _ _ H P hP h
  induction h with
  | zero =>
    rintro N x hd 𝔪 - - V _ _ π hπ ⟨φ⟩
    refine ⟨0, x, hd, ⟨Fin.elim0, ⟨by simp, fun i => i.elim0⟩, fun i => i.elim0⟩, ?_⟩
    exact (isCosocle_self hπ).of_equiv (.refl _) φ
  | succ h ih =>
    intro N x hd
    have e : N = (x 0).1 + ∑ i : Fin h, (x i.succ).1 := hd.symm.trans (Fin.sum_univ_succ _)
    subst e
    rintro 𝔪 hL hm V _ _ π hπ ⟨φ⟩
    let tail : Fin h → IrrGL (k := k) := fun i => x i.succ
    let n := ∑ i, (tail i).1
    let τ := prodIrr tail (N := n) rfl
    have hτs : IsSmooth τ := isSmooth_prodIrr tail rfl
    have split : Nonempty ((prod₂ (x 0).rep τ).Equiv (prodIrr x hd)) :=
      GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ
        (fun a => (x a).1) hd (X := fun a => (x a).2.rep.V) fun a => (x a).rep
    obtain ⟨ψ⟩ := split
    have χ : π.Equiv (prod₂ (x 0).rep τ) := φ.trans ψ.symm
    have hτi : τ.IsIrreducible := GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ k (x 0).1 n _ _ V (x 0).rep τ π
      (x 0).2.rep.smooth (x 0).2.rep.irr hτs hπ ⟨χ⟩
    have hτ : IsL (∑ i : Fin h, 𝔪 i.succ) τ :=
      ih n tail rfl (fun i => 𝔪 i.succ) (fun i => hL i.succ) (fun i => hm i.succ) _ τ hτi
        ⟨Representation.Equiv.refl τ⟩
    obtain ⟨y, hy⟩ := hP (∑ j, 𝔪 j) fun Δ hΔ => by
      obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 hΔ
      exact hm j Δ hj
    have hsum := Fin.sum_univ_succ 𝔪
    have hy' : IsL (𝔪 0 + ∑ i : Fin h, 𝔪 i.succ) y.rep := hsum ▸ hy
    exact hsum.symm ▸ isL_add_of_equiv H (x 0) y τ hτs hτi (hL 0) hτ hy' π hπ χ

end GlobalTheory.LocGL.IrrProdL

end
