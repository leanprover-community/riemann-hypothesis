module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotDivLatMulLatHomAt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsCosetSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJetsOfTranslateJets

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.LiftTypePrime.Jets (intAt_mul intAt_sum intAt_of_isIntegral isIntegral_exp)
open GlobalTheory.MomT.CosetSum

noncomputable section

namespace GlobalTheory.DatumJets


variable {p : ℕ} [Fact p.Prime] {lam : TaylorLogMetric.Qbar →+* ℂ_[p]}



variable {X : Fields} {a b : ℕ}


theorem map_jetSum {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) {cA c : ℕ}
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N')
    (hcA0 : 0 < cA) (hc0 : 0 < c) (Ξ : HomE X.E a b → X.K) {e : DVar X.Tau a b →₀ ℕ} (he : e ∈ RatIdx A S cA c N N' Ξ) :
    A.σ₀ (jetSum A S cA c N N' Ξ e) = (A.chiF a b N N')⁻¹ *
      latSum (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) fun x => A.σ₀ (Ξ x) * jetC A.cD (A.thInd S N N' c x) e := by
  have := GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S N N' cA c hN.1 hN'.1 hcA0 hc0
  have := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)

  rw [jetSum, latSum, latSum, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  generalize Function.surjInv (Submodule.Quotient.mk_surjective _) z = x
  by_cases h0 : Ξ x = 0
  · simp [h0]
  · have h := he x x.2 h0
    rw [map_mul, Amb.jetK, desc, dite_eq_left h, h.choose_spec]
    ring

end GlobalTheory.DatumJets
