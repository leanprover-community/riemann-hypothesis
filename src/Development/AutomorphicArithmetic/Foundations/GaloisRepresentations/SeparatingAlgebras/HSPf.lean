module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

noncomputable section

namespace UpperTheory.Gal.Gen

theorem hS_pf : HS := by
  classical
  intro X _ B V hV
  let L := WithLp.linearEquiv 2 ℂ (X → ℂ)
  let V' : Submodule ℂ (EuclideanSpace ℂ X) := V.map (L.symm : (X → ℂ) →ₗ[ℂ] EuclideanSpace ℂ X)
  have hfr : Module.finrank ℂ V' = Module.finrank ℂ V := LinearEquiv.finrank_map_eq L.symm V
  let e := stdOrthonormalBasis ℂ V'
  let f : Fin (Module.finrank ℂ V') → EuclideanSpace ℂ X := fun i => (e i : EuclideanSpace ℂ X)
  have hf : Orthonormal ℂ f := e.orthonormal.comp_linearIsometry V'.subtypeₗᵢ
  have hfix : ∀ i x, ∑ y, B x y * f i y = f i x := by
    intro i x
    obtain ⟨v, hv, hvf⟩ := (e i).2
    have h1 : ∀ y, f i y = v y := by
      intro y
      have : f i = L.symm v := hvf.symm
      rw [this]
      rfl
    have h2 := congrFun (hV v hv) x
    simp only [Matrix.mulVec, dotProduct] at h2
    simp only [h1]
    exact h2
  let r : X → EuclideanSpace ℂ X := fun x => WithLp.toLp 2 (fun y => starRingEnd ℂ (B x y))
  have hinner : ∀ i x, inner ℂ (r x) (f i) = f i x := by
    intro i x
    rw [← hfix i x, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [r, RCLike.inner_apply, mul_comm]
  have hbessel : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ ∑ y, ‖B x y‖ ^ 2 := by
    intro x
    have h := hf.sum_inner_products_le (x := r x) (s := Finset.univ)
    have h3 : ‖r x‖ ^ 2 = ∑ y, ‖B x y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [r]
    rw [h3] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_inner_symm, hinner]
  have hone : ∀ i, ∑ x, ‖f i x‖ ^ 2 = 1 := by
    intro i
    rw [← EuclideanSpace.norm_sq_eq, hf.1 i]
    simp
  calc (Module.finrank ℂ V : ℝ) = ∑ i : Fin (Module.finrank ℂ V'), ∑ x, ‖f i x‖ ^ 2 := by
        simp [hone, hfr]
    _ = ∑ x, ∑ i, ‖f i x‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ x, ∑ y, ‖B x y‖ ^ 2 := Finset.sum_le_sum fun x _ => hbessel x

end UpperTheory.Gal.Gen

end
