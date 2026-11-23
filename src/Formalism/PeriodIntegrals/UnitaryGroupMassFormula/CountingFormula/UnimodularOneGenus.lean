module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.PairUnitLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsIsomSelfDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ExistsTraceNotMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.StdLatEqSpan
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.UG

open Formalism.HermitianLattices.Ext.L3.WA

theorem unimodOneGenus_of (hP : PairUnitLoc) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.UnimodOneGenus := by
  intro K _ _ _ V _ _ _ _ _ h hK hs hnd L M hLl hMl hLu hMu p hp
  have hstar : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
    PI.UG.W.star_mem_range K
  have huL := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar L hLl.fg).2.mp hLu p hp
  have huM := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs hstar M hMl.fg).2.mp hMu p hp
  have hS := isHermSemilocal_locRing hK hp
  have hLfull : Submodule.IsFullLattice K L :=
    { toIsLattice := hLl
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs hnd hLl hLu }
  have hMfull : Submodule.IsFullLattice K M :=
    { toIsLattice := hMl
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs hnd hMl hMu }
  have hL' := isSelfDualMod_loc hLfull hp.isPrime huL
  have hM' := isSelfDualMod_loc hMfull hp.isPrime huM
  obtain ⟨g, hg, hiff⟩ := exists_isom_selfDual hS hs hnd
    (fun w y hyw hw hy => hP K hK p hp V h hs w y hyw hw hy) hL' hM'
  refine ⟨g, hg, ?_⟩
  ext w
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hiff v).1 hv
  · intro hw
    refine ⟨g.symm w, (hiff _).2 ?_, by simp⟩
    simpa using hw

theorem unimodular_one_genus : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.UnimodOneGenus :=
  unimodOneGenus_of pair_unit_local

end PI.UnitaryGroupMassFormula.CntFormula.UG
