module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum


noncomputable section

namespace GlobalTheory.SingleDatum.BasePair

variable {D : D7}

theorem placeIdem_mul_eq_zero {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hne : v' ≠ v) : ε' * ε = 0 := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', rfl, h1', h2'⟩ := h'
  have e : α' * α = 0 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw; rw [h2' w hne.symm, zero_mul]
    · rw [h2 w hw, mul_zero]
  show pairA D.host.F 0 α' * pairA D.host.F 0 α = 0
  have e2 : pairA D.host.F 0 α' * pairA D.host.F 0 α = pairA D.host.F 0 (α' * α) := Prod.ext (mul_zero _) rfl
  rw [e2, e]
  rfl

end GlobalTheory.SingleDatum.BasePair

