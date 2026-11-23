module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.KBsLev
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical



attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

theorem mok0 {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
    {S : Finset (Pl E)} (F₀ : Frame0 hR π S) : MLM.MOk F₀.d₀ := by
  have h0 : ∀ w, w ∉ F₀.d₀.T := fun w => by rw [F₀.T₀]; exact Finset.notMem_empty w
  have hlev : ∀ w ∈ F₀.d₀.Bad, GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (F₀.d₀.KB w) := fun w hw => by
    have h := F₀.levFam.1 w
    have e : F₀.d₀.KU w = F₀.d₀.KB w :=
      (if_neg (h0 w)).trans ((if_neg fun h' => Finset.disjoint_left.1 F₀.ok₀.disj.2.2 h' hw).trans (if_pos hw))
    rwa [e] at h
  refine ⟨fun w hw => absurd hw (h0 w), fun w hw => ⟨(F₀.S₀ w hw).2, fun g => ?_, F₀.K'_lev w hw⟩,
    fun w hw hs => ⟨hlev w hw, fun a ha => ?_⟩, fun w hw hs => ⟨F₀.kB w, F₀.kB_pos w hw hs, hlev w hw, fun γ => ?_, fun a ha => ?_⟩⟩
  · unfold UL
    rw [if_pos (F₀.S₀ w hw).2]
    exact Subgroup.mem_top g
  · rw [F₀.fix_def a ha w, if_pos hw, if_pos hs]
  · have e : {γ : UL n w | γ.1 ∈ MB.congK n w (F₀.kB w)} =
        (((GlobalTheory.PrincCong.congSub w n (F₀.kB w)).subgroupOf (UL n w) : Subgroup (UL n w)) : Set (UL n w)) :=
      Set.ext fun x => (GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) x.1).symm
    rw [F₀.KB_def w, if_pos hw, if_neg hs, e, Subgroup.closure_eq]
    exact GlobalTheory.PrincCong.mem_congSub_iff w n (F₀.kB w) γ.1
  · rw [F₀.fix_def a ha w, if_pos hw, if_neg hs]

end UpperTheory.HeckeLevelFrameExistence

end
