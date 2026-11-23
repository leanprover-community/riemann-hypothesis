module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist

open ValuativeRel in
theorem mulH_inv_mem_Lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {c : k} {κ : GL (Fin n) k}
    (hκ : κ ∈ GlobalTheory.SplitWeil.KO k (Fin n)) {l : Multiplicative (Fin n → k)} (hl : l ∈ Lc n c) :
    mulH κ⁻¹ l ∈ Lc n c := by
  obtain ⟨g, rfl⟩ := hκ
  have hl' : ∀ i, c * l.toAdd i ∈ 𝒪[k] := hl
  have hent : ∀ a b, (((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b ∈ 𝒪[k] := by
    intro a b
    rw [← map_inv]
    exact (((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) a b).2
  show ∀ j, c * ((((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ l.toAdd) j ∈ 𝒪[k]
  intro j
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [mul_left_comm]
  exact mul_mem (hent j i) (hl' i)

theorem mulH_mulH_inv {k : Type} [Field k] {n : ℕ} (κ : GL (Fin n) k)
    (l : Multiplicative (Fin n → k)) : mulH κ (mulH κ⁻¹ l) = l := by
  show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec
    (((κ⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec l.toAdd)) = l
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rfl

theorem twKer_Lc_le_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  intro k _ _ _ _ n X _ _ ρ c κ hκ x hx
  unfold GlobalTheory.PRep.twKer at hx ⊢
  refine Submodule.span_le.2 ?_ hx
  rintro w ⟨m, v, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨mulH κ⁻¹ m, mulH_inv_mem_Lc hκ m.2⟩, v, ?_⟩
  simp [mulH_mulH_inv]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist
