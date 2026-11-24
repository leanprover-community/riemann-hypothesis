module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdemOffOrth

theorem symplO_compl_half : ∀ (D : D7) (S T : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ w x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → symplO S T ((1 - e - cA D e) • w) x = 0 := by
  intro D S T P e he w x hx
  have h1 : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have h2 : e * cA D e = 0 := he.2
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hz : symplO S T (0 : WO S T) x = 0 := by
    have := GlobalTheory.BigDat.symplO_cA_smul S T (0 : AE D) w x
    rw [map_zero, zero_smul, zero_smul, GlobalTheory.BigDat.symplO_zero_right'] at this
    exact this.symm
  rcases hx with hx | hx
  · have hxe : x = cA D (cA D e) • x := by
      rw [GlobalTheory.DualPairCheck.cA_cA]; exact (GlobalTheory.BigDat.smul_of_isHalf hx).symm
    rw [hxe, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : cA D e * (1 - e - cA D e) = 0 := by linear_combination -c1 - (mul_comm e (cA D e) ▸ h2 : cA D e * e = 0)
    rw [this, zero_smul]; exact hz
  · rw [← GlobalTheory.BigDat.smul_of_isHalf hx, GlobalTheory.BigDat.symplO_cA_smul, smul_smul]
    have : e * (1 - e - cA D e) = 0 := by linear_combination -h1 - h2
    rw [this, zero_smul]; exact hz

end GlobalTheory.IdemOffOrth
