module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.MemIntROfFinPart
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}



theorem exists_intOpen (V : HSp D) : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
    ∀ k ∈ U, ∀ i j, finPart D (mt V k i j) ∈ intAE D := by
  have hfc : Continuous (finPart D) := GlobalTheory.Member.continuous_finPart D
  have hint : ∀ (A B : Mx D V.rank V.rank), (∀ i j, finPart D (A i j) ∈ intAE D) → (∀ i j, finPart D (B i j) ∈ intAE D) →
      ∀ i j, finPart D ((A * B) i j) ∈ intAE D := by
    intro A B hA hB i j

    rw [Matrix.mul_apply, map_sum]
    exact sum_mem fun l _ => by rw [map_mul]; exact GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hA i l) (hB l j)
  have hone : ∀ i j, finPart D ((1 : Mx D V.rank V.rank) i j) ∈ intAE D := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]; exact (by simpa using GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE (D := D) 1)
    · rw [map_zero]; exact zero_mem _
  let U : Subgroup (GA D V) :=
    { carrier := {k | (∀ i j, finPart D (mt V k i j) ∈ intAE D) ∧ ∀ i j, finPart D (mt V k⁻¹ i j) ∈ intAE D}
      one_mem' := by
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [show mt V 1 = 1 from rfl]; exact hone i j
        · rw [inv_one, show mt V 1 = 1 from rfl]; exact hone i j
      mul_mem' := by
        rintro k l ⟨hk, hk'⟩ ⟨hl, hl'⟩
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [show mt V (k * l) = mt V k * mt V l from rfl]; exact hint _ _ hk hl i j
        · rw [mul_inv_rev, show mt V (l⁻¹ * k⁻¹) = mt V l⁻¹ * mt V k⁻¹ from rfl]; exact hint _ _ hl' hk' i j
      inv_mem' := by
        rintro k ⟨hk, hk'⟩
        exact ⟨hk', by simpa using hk⟩ }
  refine ⟨U, ?_, fun k hk => hk.1⟩
  have hmt : Continuous (mt V) := GlobalTheory.MixModel.continuous_mt V
  have hmti : Continuous fun k : GA D V => mt V k⁻¹ := hmt.comp continuous_inv
  have hopen : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have h1 := GlobalTheory.CompanionTheory.Ipf.Bdd.isOpen_nsmul_mem (D := D) 1
    simp only [one_nsmul] at h1
    exact h1
  have e : (U : Set (GA D V)) = (⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k i j)) ⁻¹' {z | z ∈ intAE D}) ∩
      ⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k⁻¹ i j)) ⁻¹' {z | z ∈ intAE D} := by
    ext k; simp [U]
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact hopen.preimage (hfc.comp ((continuous_apply j).comp ((continuous_apply i).comp hmt)))
  · exact hopen.preimage (hfc.comp ((continuous_apply j).comp ((continuous_apply i).comp hmti)))

end PositivityTheory.Rg.Rsw.L.LLatBound

end
