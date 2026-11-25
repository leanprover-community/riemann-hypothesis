module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

variable {F : Type} [Field F] [NumberField F]

theorem fst_eq (x : AF F) : fstA F x = x.1 := rfl
theorem snd_eq (x : AF F) : sndA F x = x.2 := rfl

theorem idF_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε.1 = 1 := hε.1

open Classical in
theorem idF_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) (v : HeightOneSpectrum (𝓞 F)) :
    ε.2 v = if v ∈ S then 1 else 0 := hε.2 v

theorem idF_mul {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) : ε * ε = ε := by
  classical
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_)
  · change ε.1 * ε.1 = ε.1
    rw [idF_fst hε, one_mul]
  · change ε.2 v * ε.2 v = ε.2 v
    rw [idF_snd hε v]
    split_ifs <;> simp

theorem ker_fst {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0) :
    y.1 = 0 := by
  have h : (ε * y).1 = 0 := by rw [hy]; rfl
  change ε.1 * y.1 = 0 at h
  rwa [idF_fst hε, one_mul] at h

theorem ker_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {y : AF F} (hy : ε * y = 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : y.2 v = 0 := by
  classical
  have h : (ε * y).2 v = 0 := by rw [hy]; rfl
  change ε.2 v * y.2 v = 0 at h
  rwa [idF_snd hε v, if_pos hv, one_mul] at h

theorem fix_snd {S : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsIdF S ε) {h : AF F} (hh : ε * h = h)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : h.2 v = 0 := by
  classical
  have h' : (ε * h).2 v = h.2 v := by rw [hh]
  change ε.2 v * h.2 v = h.2 v at h'
  rw [idF_snd hε v, if_neg hv, zero_mul] at h'
  exact h'.symm

theorem fix_mul_ker {ε h y : AF F} (hε : ε * ε = ε) (hh : ε * h = h) (hy : ε * y = 0) : h * y = 0 := by
  calc h * y = (ε * h) * y := by rw [hh]
    _ = h * (ε * y) := by ring
    _ = 0 := by rw [hy, mul_zero]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
