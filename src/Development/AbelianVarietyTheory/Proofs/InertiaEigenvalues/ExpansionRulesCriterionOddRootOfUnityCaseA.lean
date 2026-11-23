module

public import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpCritPOf
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LMemMaxOL
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.ExpansionsOdd



theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL),
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) ∧
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm hN l _ K LL hA
  obtain ⟨p1, -, p3, p4, p5, -, -, -, p9, -⟩ := hN
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.OLC.complete_max LL
  have hLT := GlobalTheory.LevelClauseOdd.main D HW F Cm p4 p9 l K LL hA
  have C := ((Cm l).C K 1 LL hA.2.2).tie
  have hs : ((HW l).W K 1 LL hA.2.2).s = 1 := (HW l).W_s K 1 LL hA.2.2
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie _ hs C
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) := p9 l K 1 LL hA.2.2
  refine ⟨fun hCA => ?_, Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of _ hLT.1 hG.1 hG.2, ?_⟩
  · have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA.2.2) :=
      (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA.2.2))) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA.1)).1
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of _ hring hCA
  · have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
      rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
    have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 :=
      GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL
    have hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hA.2.2) := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ h9
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_of _ Subtype.val_injective hlm (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL)
      (p1 l K 1 LL hA.2.2) (p3 l K 1 LL hA.2.2) hLT.1 (p5 l K 1 LL hA.2.2) h9 hD hB C
      (p4 l K 1 LL hA.2.2) hLT.2

end GlobalTheory.ExpansionsOdd
