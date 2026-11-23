module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibPhi

private theorem one_add_colMat_apply_eq_zero_of_ne_last (k : Type) [Field k] (n : ℕ) (v : Fin n → k)
    {r c : Fin (n + 1)} (hc : c ≠ Fin.last n) (hrc : r ≠ c) :
    (1 + GlobalTheory.BZMir.colMat k n v) r c = 0 := by
  simp only [Matrix.add_apply, Matrix.one_apply, GlobalTheory.BZMir.colMat, ite_eq_right hc,
    ite_eq_right hrc, add_zero]

theorem mirUin_le_HGP (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) :
    MirUin k (m + j) ≤ GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
  intro g hg
  unfold GlobalTheory.BZMir.MirUin at hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨v, hv⟩ := hg
  change (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro x y b a hxy
  obtain ⟨rfl, rfl⟩ := Bool.lt_iff.mp hxy
  have hmat : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k (m + j) (Multiplicative.toAdd v) := by
    rw [← hv]
    rfl
  rw [hmat]
  apply one_add_colMat_apply_eq_zero_of_ne_last k (m + j) _
    (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a)
  intro h
  have h' := congrArg Fin.val h
  rw [GlobalTheory.CompanionTheory.LeibPhi.blockIndex_false_val,
    GlobalTheory.CompanionTheory.LeibPhi.blockIndex_true_val] at h'
  have ha := a.isLt
  omega

end GlobalTheory.CompanionTheory.LeibPhi
