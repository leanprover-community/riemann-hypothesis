module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem exists_hpg_mid_levi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (p : Mir k (i + t)) :
    ∃ h ∈ HPG k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), ∃ v : Fin t → k,
      p = h * (uM k (i + t) (midV k i t v) * levi k (i + t) κ) := by
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k (i + t)
    (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k (i + t)
      (p * (GlobalTheory.BZMir.levi k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) p))⁻¹)
      (by rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]))
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y *
      GlobalTheory.BZMir.levi k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) p) := by
    rw [← hy, inv_mul_cancel_right]
  obtain ⟨q, κ, hκ, hgq⟩ := GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact k i t (GlobalTheory.BZMir.mirabolicProjection k (i + t) p)
  obtain ⟨x, v, hxv⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_top_mid k i t
    ((((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ y)
  obtain ⟨hq, -⟩ := GlobalTheory.T.levi_block_mem_parabolic k i t q
  obtain ⟨hx, -⟩ := GlobalTheory.T.unipotent_top_mem_parabolic k i t x
  refine ⟨GlobalTheory.BZMir.levi k (i + t) q * GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x),
    mul_mem hq hx, κ, hκ, v, ?_⟩
  have key : GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) q =
      GlobalTheory.BZMir.levi k (i + t) q * GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t)
        ((((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ y) := by
    rw [GlobalTheory.CompanionTheory.BZPsiPG.levi_mul_uM, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  rw [hp, hgq, map_mul, ← mul_assoc (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y), key, hxv,
    GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
  simp only [mul_assoc]

theorem eq_zero_of_fibV_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (a : cIndSpace (HPG k i t) (hRep τ σ)),
    (∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), fibV a κ = 0) → a = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ a ha
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext p
  obtain ⟨h, hh, κ, hκ, v, rfl⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_hpg_mid_levi k i t p
  have hfe : a.1.1.1 (h * (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) κ)) =
      GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ ⟨h, hh⟩ (a.1.1.1 (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t)
        (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) * GlobalTheory.BZMir.levi k (i + t) κ)) :=
    a.1.1.2 ⟨h, hh⟩ _
  have hz : a.1.1.1 (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) κ) = 0 := congrFun (ha κ hκ) v
  show a.1.1.1 _ = (0 : V ⊗[ℂ] W)
  rw [hfe, hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
