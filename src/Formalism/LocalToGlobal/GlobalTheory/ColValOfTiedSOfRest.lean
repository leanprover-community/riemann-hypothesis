module

public import Formalism.LocalToGlobal.GlobalTheory.ClassesLevelZeroNonempty
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hT_self_of_on {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
    (b : Module.Basis (Fin S.rank) E S.V) (hb : ∀ a a', S.hT (b a) (b a') = if a = a' then 1 else 0) (y : S.V) :
    S.hT y y = ∑ a, star (b.repr y a) * b.repr y a := by
  conv_lhs => rw [← b.sum_repr y]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, hb,
  smul_eq_mul, starRingEnd_apply]
  simp [mul_ite, Finset.sum_ite_eq]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem posFrame_of_std (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : PosFrame D := by
  obtain ⟨b, hb, -⟩ := h
  intro σ
  refine ⟨(b.toMatrix (D.sp.X 0).frame).map σ, ?_, ?_⟩
  · haveI := b.invertibleToMatrix (D.sp.X 0).frame
    have hu : IsUnit (σ (b.toMatrix (D.sp.X 0).frame).det) :=
      (Matrix.isUnit_det_of_invertible _).map σ
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at hu
  · intro y
    have hrepr : ∀ i, ((b.toMatrix (D.sp.X 0).frame).map σ *ᵥ
        fun j => σ ((D.sp.X 0).frame.repr y j)) i = σ (b.repr y i) := by
      intro i
      rw [← (D.sp.X 0).frame.toMatrix_mulVec_repr b y, RingHom.map_mulVec]
      rfl
    simp only [hrepr]

    rw [hT_self_of_on (D.sp.X 0) b hb y, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, host_emb_star, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem colBase_of_sym {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (u : D.what₂.Word)
    (rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL)) : ∃ B : ColBase D u, B.rho = rho :=
  ColBase_exists D u (posFrame_of_std D (F.herm.std.1 0 (Nat.zero_le _))) rho
    (fun c => (D.clsLat_lat u 0 c).span_eq_top)

theorem colValOfTiedS_of_rest'
    (h : ∀ D : D7, Formalism.L2.Forms.ColsTiedSym D → Formalism.MainNotions.flipTwoThree.adm3 D → ∀ u : D.what₂.Word,
      ∃ rho : D.what₂.Tau → (D.host.E →+* D.what₂.LL), ∀ B : ColBase D u, B.rho = rho → ColRest B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility := by
  refine colValOfTiedS_of_rest fun D F ha u => ?_
  obtain ⟨rho, hr⟩ := h D F ha u
  obtain ⟨B, hB⟩ := colBase_of_sym F u rho
  exact ⟨B, hr B hB⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
