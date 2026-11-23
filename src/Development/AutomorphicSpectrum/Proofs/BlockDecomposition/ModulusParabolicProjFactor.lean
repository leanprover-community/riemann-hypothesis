module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
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

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem det_hgp (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (h : MirabolicParabolic k m j) :
    GeneralLinearGroup.det ((h : Mir k (m + j)) : GL (Fin (m + j + 1)) k) =
      GeneralLinearGroup.det (gpProj k m j h).1 *
        GeneralLinearGroup.det ((gpProj k m j h).2 : GL (Fin (j + 1)) k) := by
  let f : Fin m ⊕ Fin (j + 1) → Fin (m + j + 1) :=
    Sum.elim (fun a => GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩)
      (fun b => GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) hab <;>
      have hs := (GlobalTheory.BZMir.Leib.eGP m j).injective hab <;>
      simp_all [Sigma.mk.inj_iff]
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simp only [Fintype.card_sum, Fintype.card_fin]; omega⟩
  have hA : ∀ a b : Fin m,
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨false, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨false, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) false a b
  have hD : ∀ a b : Fin (j + 1),
      (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) : Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b =
        (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (GlobalTheory.BZMir.Leib.eGP m j ⟨true, a⟩) (GlobalTheory.BZMir.Leib.eGP m j ⟨true, b⟩) :=
    fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j h) true a b
  have hzero := (GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff k m j (h : GlobalTheory.BZMir.Mir k (m + j))).mp h.2
  have hsub : (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k).submatrix (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
      Matrix.fromBlocks
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)
        (Matrix.of fun a b => (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
          Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) (f (Sum.inl a)) (f (Sum.inr b)))
        0
        (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    ext (a | a) (b | b)
    · exact (hA a b).symm
    · rfl
    · exact hzero a b
    · exact (hD a b).symm
  have key : Matrix.det (((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).1 : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *
        Matrix.det (((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) :
          Matrix (Fin (j + 1)) (Fin (j + 1)) k) := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf), hsub, Matrix.det_fromBlocks_zero₂₁]
  ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  exact key

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (s : ℝ) (h : MirabolicParabolic k m j),
    dpowM (m + j) s (h : Mir k (m + j)) = dpow m s (gpProj k m j h).1 * dpowM j s (gpProj k m j h).2 := by
  intro k _ _ _ _ m j s h
  have h1 : GlobalTheory.RgGu.Leib.dpowM (m + j) s (h : GlobalTheory.BZMir.Mir k (m + j)) =
      GlobalTheory.BZMir.Leib.dpow (m + j + 1) s ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) := rfl
  have h2 : GlobalTheory.RgGu.Leib.dpowM j s (GlobalTheory.BZMir.Leib.gpProj k m j h).2 =
      GlobalTheory.BZMir.Leib.dpow (j + 1) s ((GlobalTheory.BZMir.Leib.gpProj k m j h).2 : GL (Fin (j + 1)) k) := rfl
  have h3 : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  rw [h1, h2, h3, h3, h3, GlobalTheory.CompanionTheory.LeibPhi.det_hgp, map_mul]

end GlobalTheory.CompanionTheory.LeibPhi

end
