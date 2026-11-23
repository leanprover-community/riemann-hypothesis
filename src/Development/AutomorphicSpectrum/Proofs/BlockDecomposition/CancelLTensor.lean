module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProduct
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

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovComp

theorem cancel_lTensor (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    (B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁]
    {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) (w : B₁ ⊗[B] (B ⊗[A] K₁)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₀ ((d.baseChange B).lTensor B₁ w) =
      d.lTensor B₁ (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₁ w) := by
  induction w with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b t =>
    induction t with
    | add x y hx hy => simp only [map_add (f := _), TensorProduct.tmul_add, hx, hy]
    | tmul c k => simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.smul_tmul']

theorem cov_comp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B](B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁] (r : ℕ → A), Pf p A → Pf p B → IsRt p r → Cov p r B → Cov p (fun k => algebraMap A B (r k)) B₁ → Cov p r B₁ := by
  intro p _ A _ B _ _ B₁ _ _ _ _ r hA hB hr h1 h2
  unfold Cov at h1 h2 ⊢
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  have e1 : Pf p (B ⊗[A] K₁) := PerfectRing.pf_tensor p A B K₁ hA hB hK₁
  have e0 : Pf p (B ⊗[A] K₀) := PerfectRing.pf_tensor p A B K₀ hA hB hK₀
  have e2 : Good p (fun k => algebraMap A B (r k)) (d.baseChange B) :=
    GoodBaseChange.good_baseChange p A B r K₁ K₀ d hd
  have hz' : (1 : B₁) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] z) ∈ (LinearMap.lTensor B₁ (d.baseChange B)).range := by
    obtain ⟨w, hw⟩ := hz
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₁).symm w, ?_⟩
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B₁ B₁ K₀).injective
    rw [cancel_lTensor, LinearEquiv.apply_symm_apply, hw]
    simp
  have hB' := h2 _ _ e1 e0 (d.baseChange B) e2 _ hz' (k + 1)
  have h3 : (1 : B) ⊗ₜ[A] (r (k + 1) • z) ∈ (LinearMap.lTensor B d).range := by
    obtain ⟨v, hv⟩ := hB'
    refine ⟨v, ?_⟩
    change (d.baseChange B) v = _
    rw [hv, algebraMap_smul, ← TensorProduct.tmul_smul]
  have h4 := h1 K₁ K₀ hK₁ hK₀ d hd (r (k + 1) • z) h3 (k + 1)
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    rw [← hr k, ← sq, ← pow_add, Nat.sub_add_cancel hp]
  rw [hrk, mul_smul, mul_smul]
  exact Submodule.smul_mem _ _ h4

end GlobalTheory.CompanionTheory.CovComp
