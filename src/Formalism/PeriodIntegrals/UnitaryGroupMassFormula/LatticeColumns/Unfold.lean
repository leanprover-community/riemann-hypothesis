module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ClassCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open MeasureTheory
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def MassUnfoldGen : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    (X.measW u).IsTextNorm →
    CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) →
    ∀ U : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsCompact (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) →
      IsOpen (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) →
      MassFinite (GamHA X u) U →
      ∀ 𝓕 : Set ↥(Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
        IsFundamentalDomain (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕 (X.measW u).μH →
        (X.measW u).μH 𝓕 = (X.measW u).μHinf Set.univ *
          (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) *
          ENNReal.ofReal (massCl (GamHA X u) U)

theorem massCl_nonneg {G : Type} [Group G] (Γ K : Subgroup G) : 0 ≤ massCl Γ K := by
  unfold massCl
  exact finsum_nonneg fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem unfoldGenStep_of (hM : MassUnfoldGen) (hH : MassDataMassesW.HinfCompact) (hF : MassDataMassesW.FDExistsH)
    (hV : MassDataMassesW.VolHTie) : UnfoldGenStep := by
  unfold UnfoldGenStep
  intro D X hb u hT U hUo hUc hMF
  have hN : (X.measW u).IsTextNorm := by
    exact X.measW_norm u
  have hC := hH X u
  have key := hM X u hN hC U hUc hUo hMF
  have hV' := hV X hb u hT
  obtain ⟨𝓕, h𝓕⟩ := hF X u
  have hex : ∃ 𝓕 : Set ↥(Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsFundamentalDomain (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕
        (X.measW u).μH := ⟨𝓕, h𝓕⟩
  have hcov : covol (X.measW u).μH = ((X.measW u).μH hex.choose).toReal := by
    unfold covol
    exact dif_pos hex
  obtain ⟨-, hHi, hHf, -⟩ := hN
  haveI := hHi
  haveI := hHf
  have h1 : (X.measW u).μHinf Set.univ ≠ 0 := isOpen_univ.measure_ne_zero _ Set.univ_nonempty
  have h2 : (X.measW u).μHinf Set.univ ≠ ⊤ := (hHi.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (@isCompact_univ _ _ hC)).ne
  have h3 : (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≠ 0 := IsOpen.measure_ne_zero (X.measW u).μHf hUo ⟨1, U.one_mem⟩
  have h4 : (X.measW u).μHf (U : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) ≠ ⊤ := (hHf.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact hUc).ne
  refine ⟨?_, ?_⟩
  · rw [hcov, key hex.choose hex.choose_spec, hV', ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (massCl_nonneg _ _)]
  · rw [hV']
    exact mul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨h1, h2⟩) (ENNReal.toReal_ne_zero.mpr ⟨h3, h4⟩)

end PIW.MassDataColumns
