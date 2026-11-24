module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeOfImNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem colNorm_exists_im_ne_zero {K : Type} [Field K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (h a)

theorem colNorm_normAt_column (D : D7) (u : D.what₂.Word) (x : (D.div.Nu u).V) :
    Formalism.HermitianLatticesTheory.normAt (D.div.Nu u).b (D.div.Nu u).X (InfinitePlace.mk D.what₂.embLL) x = ‖D.jN u x‖ := by
  rw [D.nuIn_norm, normAt_sq_eq_majAt_re, (D.fm u).emb_norm, ← D.nuIn_jN, norm_eq_sqrt_re_inner (𝕜 := ℂ), D.eMu_isom]
  rfl

theorem colNorm_of_nuTie : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), R.NuTie → M.ColNorm := by
  intro D Bs A X fc s R cr M h u
  obtain ⟨L, hL⟩ := h u
  refine ⟨1, one_pos, fun φ => ?_⟩
  rw [one_mul]
  have htw : ∀ a, (InfinitePlace.mk D.what₂.embLL).embedding a = cj s (D.what₂.embLL a) := by
    rw [← R.v0]; exact R.twist
  have := fnorm_cjv_eq_norm D.what₂.LL D.what₂.embLL s htw (colNorm_exists_im_ne_zero _) (D.div.Nu u) _ L _ (R.eNu u) hL
    (D.what₂.Mu u) (D.jN u) (M.cφ u) (colNorm_normAt_column D u) (M.cφ_eq u) φ
  rw [← R.v0] at this
  exact this

end GlobalTheory.Mem.SJ
