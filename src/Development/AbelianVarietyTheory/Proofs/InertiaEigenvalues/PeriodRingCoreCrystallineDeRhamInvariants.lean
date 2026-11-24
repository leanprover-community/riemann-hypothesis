module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem Fits.invB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvB := by
  intro K b hb
  set b' : P.R.B := T.eB.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actB g b' = b' := by
    intro g
    rw [P.PD_actB]
    apply T.eB.injective
    rw [T.actB, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invB b' hfix
  refine ⟨IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c, (inf_le_left : K0 K ≤ K.1) c.2, ?_⟩
  rw [← hF.u]
  have : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem Fits.invdR {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvdR := by
  intro K b hb
  set b' : P.R.BdR := T.eD.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actdR g b' = b' := by
    intro g
    rw [P.PD_actdR]
    apply T.eD.injective
    rw [T.actD, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invdR b' hfix
  refine ⟨(c : Om l), c.2, ?_⟩
  rw [← hF.o]
  have : algebraMap (Om l) P.R.BdR (c : Om l) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem fits_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (C : Core l), Fits T C → C.InvB ∧ C.InvdR :=
  fun _ _ _ _ _ _ hF => ⟨hF.invB, hF.invdR⟩

end GlobalTheory.MemLoc
