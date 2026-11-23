module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One


open Formalism.L2.SG.NGCut.CorankRelation in
theorem corankOne_isEquivalence_nonzeroGram_terms : CorankOneIsEquivalenceOnRow := by
  intro D X Y u u' _hT
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t ∈ (Y.tO u u').nzSet, Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro t ht h
    apply ht
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos ((Formalism.L2.SG.Pf.SatGram.gterm_G Y t).trans h)]
  have hlat : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      Submodule.IsFullLattice D.host.E t.lam := fun t => ((Y.rowsOK u).1 t.lam t.mem).1.1
  have hLF : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      IsLift t.lam (lf D (X.Fu u)) := fun t => ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), IsLift t.lam t.frame :=
    fun t => t.rep.2.2.2.2.1
  refine ⟨fun t ht => ?_, fun t ht t' ht' hr h1 => ?_, fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 => ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨rfl, rfl⟩, mul_inv_cancel]
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t.frame 1 (hLF t) (hLt t) (hGv t ht)).2
      (Th_one _ _ _)
  · have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' ⊢
    rw [if_pos ⟨hlam, hlam'⟩] at h1'
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    have hth := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
    have hsym := Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
      (hGv t ht) (hGv t' ht') (frame_mem_iff t t') hth
    have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
    rw [hinv] at hsym
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' ht')).2 hsym
  · have hl1 : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl1' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr1
    have hl2 : t'.lam = t''.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have hl2' : t'.lam' = t''.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr2
    have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := h1
    have h2' : Formalism.L2.SG.TermOp.s0T t' t'' = 1 := h2
    show Formalism.L2.SG.TermOp.s0T t t'' = 1
    unfold Formalism.L2.SG.TermOp.s0T at h1' h2' ⊢
    rw [if_pos ⟨hl1, hl1'⟩] at h1'
    rw [if_pos ⟨hl2, hl2'⟩, ← hl1] at h2'
    rw [if_pos ⟨hl1.trans hl2, hl1'.trans hl2'⟩]
    have hL' : IsLift t.lam t'.frame := by rw [hl1]; exact hLt t'
    have hth1 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
      (hGv t ht)).1 h1'
    have hth2 := (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t''.frame _ (hLF t) hL'
      (hGv t' ht')).1 h2'
    have htr := Th_trans t.lam _ t.frame t'.frame t''.frame (t'.lin * t.lin⁻¹) (t''.lin * t'.lin⁻¹)
      (fun x hx => (frame_mem_iff t' t'' x).1 hx) hth1 hth2
    have hmul : (t''.lin * t'.lin⁻¹) * (t'.lin * t.lin⁻¹) = t''.lin * t.lin⁻¹ := by group
    rw [hmul] at htr
    exact (s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t''.frame _ (hLF t) (hLt t) (hGv t ht)).2 htr

end GlobalTheory.Core.One
