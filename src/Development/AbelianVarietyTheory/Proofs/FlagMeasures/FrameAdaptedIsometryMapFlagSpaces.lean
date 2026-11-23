module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
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

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem adapt_map_flag (D : D7) (T : D.host.E) (F G : LFlag (D.sp.Y 0) D.R.rS T) (g : GV D) (hg : Adapt g F G) :
    (∀ j : ℕ, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag G j) ∧
      (Xsp F).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp G := by
  have hmono : ∀ (H : LFlag (D.sp.Y 0) D.R.rS T) {a b : ℕ}, a ≤ b → Xflag H a ≤ Xflag H b := by
    intro H a b hab
    exact Submodule.span_mono (Set.image_mono fun i (hi : i.1 < a) => (lt_of_lt_of_le hi hab : i.1 < b))
  have hmem : ∀ (H : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) {j : ℕ}, i.1 < j → H.fl.e i ∈ Xflag H j := by
    intro H i j hij
    exact Submodule.subset_span ⟨i, hij, rfl⟩
  have hX : ∀ H : LFlag (D.sp.Y 0) D.R.rS T, Xsp H = Xflag H D.R.rS := by
    intro H
    show Submodule.span _ (Set.range H.fl.e) = Submodule.span _ (H.fl.e '' {i | i.1 < D.R.rS})
    congr 1
    ext x
    simp
  have hstep : ∀ i : Fin D.R.rS, g (F.fl.e i) - G.fl.e i ∈ Xflag G i.1 := by
    intro i
    have := hg.2 i.castSucc
    simpa [frame, Formalism.MainNotions.S.FlagG.fvec] using this
  have hle : ∀ j, (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag G j := by
    intro j
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    show g (F.fl.e i) ∈ Xflag G j
    have h1 := hmono G (le_of_lt hi) (hstep i)
    have h2 := hmem G i hi
    simpa using add_mem h1 h2
  have hge : ∀ j, Xflag G j ≤ (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) := by
    intro j
    induction j with
    | zero =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      exact absurd hi (Nat.not_lt_zero _)
    | succ j ih =>
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hmap : (Xflag F j).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) ≤
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.map_mono (hmono F (Nat.le_succ j))
      have h1 : g (F.fl.e i) - G.fl.e i ∈ (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        hmap (ih (hmono G hi' (hstep i)))
      have h2 : (g : (VS D).V →ₗ[D.host.E] (VS D).V) (F.fl.e i) ∈
          (Xflag F (j + 1)).map (g : (VS D).V →ₗ[D.host.E] (VS D).V) :=
        Submodule.mem_map_of_mem (hmem F i hi)
      have h3 := sub_mem h2 h1
      simp only [LinearEquiv.coe_coe, sub_sub_cancel] at h3
      exact h3
  refine ⟨fun j => le_antisymm (hle j) (hge j), ?_⟩
  rw [hX F, hX G]
  exact le_antisymm (hle _) (hge _)

end GlobalTheory
