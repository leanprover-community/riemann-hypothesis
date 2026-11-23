module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PtString

open GlobalTheory.SphPar GlobalTheory.SphGal GlobalTheory.Hk3 GlobalTheory.CuspRep Formalism.UG Polynomial
open Formalism.MainNotions.SchurIrreducible (IsSplit)

variable {D : D7}

theorem isSplit_iff_conj (P : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (P.under (𝓞 D.host.F)) ↔ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal := by
  rw [GlobalTheory.LFun.isSplit_iff, Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  constructor
  · rintro ⟨w, w', hne, h, h'⟩ e
    have e' : Formalism.DivisionValues.conjPl P = P := HeightOneSpectrum.ext e
    have a := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have b := GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h'
    rw [e', or_self] at a b
    exact hne (a.trans b.symm)
  · intro h
    exact ⟨P, Formalism.DivisionValues.conjPl P, fun e => h (congrArg HeightOneSpectrum.asIdeal e).symm, rfl,
      (GlobalTheory.LevelPlaces.under_eq_of_isConjPl (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)).symm⟩

section Sizes

variable {c q r t : ℕ} {m d : Fin c → ℕ} {B : Fin c → Multiset ℂˣ}

end Sizes

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

open GlobalTheory.DownLift GlobalTheory.DownLift.Params GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

end Real

end GlobalTheory.PtString

end
