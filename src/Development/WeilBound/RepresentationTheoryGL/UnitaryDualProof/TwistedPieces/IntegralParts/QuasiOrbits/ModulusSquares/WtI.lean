module

public import Mathlib.LinearAlgebra.Determinant
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.LaurentCoeffZero
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Nil.Orb.Mod

open PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound

variable {k : Type} [Field k] {n : ℕ}

theorem wtI [Infinite k] (P : GL (Fin n) k) (w : Fin n → ℤ) (W : Submodule k (Fin n → k))
    (hinv : ∀ t : kˣ, ∀ y ∈ W,
      Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val) y ∈ W)
    (hpos : ∀ y ∈ W, ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) :
    ∃ m : ℕ, ∀ t : kˣ,
      LinearMap.det ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict
        (hinv t)) = (t : k) ^ m := by
  classical
  have hinv' : ∀ t : kˣ, ∀ y ∈ W, gt P w t *ᵥ y ∈ W := fun t y hy => by
    have := hinv t y hy
    rwa [Matrix.toLin'_apply] at this

  let S : Set W := {y | ∃ m : ℕ, prj P w m (y : Fin n → k) = y}
  have hspan : Submodule.span k S = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hsum := sum_prj P w y
    have hmem : ∀ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) ∈ Submodule.span k S := by
      intro m _
      by_cases hm : m < 0
      · have h0 : (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) = 0 :=
          Subtype.ext (prj_neg P w m hm y (hpos y hy))
        rw [h0]; exact Submodule.zero_mem _
      · apply Submodule.subset_span
        refine ⟨m.toNat, ?_⟩
        have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
        simp only [this]
        exact prj_prj P w m y
    have : (⟨y, hy⟩ : W) = ∑ m ∈ Finset.univ.image w, (⟨prj P w m y, prj_mem P w W hinv' m y hy⟩ : W) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact hsum.symm
    rw [this]
    exact Submodule.sum_mem _ hmem
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent k S
  have hfin : Finite b := hli.finite
  let _ : Fintype b := Fintype.ofFinite b
  let B : Basis b k W := Basis.mk hli (by
    rw [Subtype.range_coe, hbspan, hspan])
  have hwt : ∀ j : b, ∃ m : ℕ, prj P w m ((j : W) : Fin n → k) = (j : W) := fun j => hbS j.2
  choose mj hmj using hwt
  refine ⟨∑ j, mj j, fun t => ?_⟩
  rw [← LinearMap.det_toMatrix B]
  have hdiag : LinearMap.toMatrix B B ((Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) *
      P⁻¹.val)).restrict (hinv t)) = diagonal (fun j => (t : k) ^ (mj j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hfj : (Matrix.toLin' (P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val)).restrict (hinv t) (B j)
        = (t : k) ^ (mj j) • B j := by
      apply Subtype.ext
      rw [LinearMap.coe_restrict_apply, Matrix.toLin'_apply, Basis.mk_apply, Submodule.coe_smul]
      have h1 := gt_prj P w t (mj j) ((j : W) : Fin n → k)
      rw [hmj j] at h1
      have h2 : ((t ^ ((mj j : ℕ) : ℤ) : kˣ) : k) = (t : k) ^ (mj j) := by simp [zpow_natCast]
      rw [h2] at h1
      exact h1
    rw [hfj, map_smul, Basis.repr_self, diagonal_apply]
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hdiag, det_diagonal, Finset.prod_pow_eq_pow_sum]

end PositivityTheory.RgUd.TP.Nil.Orb.Mod
