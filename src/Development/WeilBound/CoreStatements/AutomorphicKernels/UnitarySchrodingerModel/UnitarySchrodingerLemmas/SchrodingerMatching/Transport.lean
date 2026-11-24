module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwMatch

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.SiegelND

section Transport

variable {D : D7} {n : ℕ}

def hermToME : hermA D n ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n where
  toFun := hermTo
  invFun := hermFrom
  left_inv := hermFrom_hermTo
  right_inv := hermTo_hermFrom
  measurable_toFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermTo.measurable
  measurable_invFun := by
    haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
    haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
    haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n) := ⟨rfl⟩
    exact continuous_hermFrom.measurable

theorem integral_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) :
    ∫ b, W b ∂(lam.map hermTo) = ∫ b, W (hermTo b) ∂lam :=
  (hermToME (D := D) (n := n)).measurableEmbedding.integral_map W

theorem integrable_map_hermTo (lam : Measure (hermA D n))
    (W : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF D.host.F) D.sp.cm.sig n → ℂ) (h : Integrable (fun b => W (hermTo b)) lam) :
    Integrable W (lam.map hermTo) :=
  ((hermToME (D := D) (n := n)).measurableEmbedding.integrable_map_iff).2 h

end Transport

end PositivityTheory.PfSWUS.SwMatch

end
