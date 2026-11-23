module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.GoodSplitFam

theorem good_split_pl : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ P, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P ∧ A3.A.q P0 ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW e P hG hP
  obtain ⟨hC, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW e
  obtain ⟨hQ0, -, -, hfam⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev
  have hSb : R.Sb = R.Pg := hW.allPl
  have hci : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (Formalism.DivisionValues.conjPl P).asIdeal :=
    GlobalTheory.InertValLab.conjIdeal_eq_conjPl P
  have hsplit : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hci]
      intro h
      exact hP (HeightOneSpectrum.ext h)
    · intro hm
      have hm' : P ∈ R.Pg := by rw [← hSb]; exact hm
      exact (hG P (Or.inl hm')).1 rfl
    · intro Q hQ h
      rw [hci] at h
      have hQ' : Q ∈ R.Pg := by rw [← hSb]; exact hQ
      have hQe : Q = Formalism.DivisionValues.conjPl P := HeightOneSpectrum.ext h
      apply (hG Q (Or.inl hQ')).2
      rw [GlobalTheory.GoodPrimes.isConjPl_iff, hQe, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  obtain ⟨P0, hP0⟩ := hC.fam.pl_onto P hsplit
  obtain ⟨gramR, c0R, c0L, htie⟩ := hC.fam.tie
  have hok : P0 ∈ A3.A.ok A3.A.μ0 := by
    rw [htie.ok, hQ0, hP0]
    simpa using hsplit
  refine ⟨P0, hok, hP0, ?_⟩
  rw [(hfam hC.fam A3.A.μ0 P0 hok).2.2]
  intro h0
  exact (R.pl P0).ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)

end GlobalTheory.GoodSplitFam
