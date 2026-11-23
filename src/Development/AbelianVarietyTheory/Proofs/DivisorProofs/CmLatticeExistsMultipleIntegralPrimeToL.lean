module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasSumZeroOfTwoLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdeleStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.LatticeUp

theorem exists_mul_integral : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ), l.Prime →
    OneOver l y → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((M : E) * x) := by
  intro E _ _ l c y hl hy
  obtain ⟨M, hM, hMv⟩ := GlobalTheory.T.exists_denominator_prime_to_l_finiteAdele E l (y : Af E) hl fun w hw => by rw [hy w hw, map_one]
  refine ⟨M, hM, fun x hx => ?_⟩
  have hx' : algebraMap E (Af E) x * (↑y⁻¹ : Af E) ∈ hatO c := hx
  have key : algebraMap E (Af E) ((M : E) * x) =
      (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * (algebraMap E (Af E) (M : E) * (y : Af E)) := by
    have hyy : (↑y⁻¹ : Af E) * (y : Af E) = 1 := y.inv_mul
    rw [map_mul]
    calc algebraMap E (Af E) (M : E) * algebraMap E (Af E) x
        = algebraMap E (Af E) (M : E) * algebraMap E (Af E) x * ((↑y⁻¹ : Af E) * (y : Af E)) := by rw [hyy, mul_one]
      _ = _ := by ring
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((M : E) * x) fun v => by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((M : E) * x)]
    have h1 := GlobalTheory.CMVal.ObjModel.hatO_integral hx' v
    have h2 := hMv v
    have : (algebraMap E (Af E) ((M : E) * x)) v =
        (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) v * (algebraMap E (Af E) (M : E) * (y : Af E)) v := by
      rw [key]; rfl
    rw [show ((((M : E) * x : E)) : v.adicCompletion E) = (algebraMap E (Af E) ((M : E) * x)) v from rfl, this, map_mul]
    exact mul_le_one' h1 h2
  rw [← hb]
  exact (b.isIntegral_coe)

end GlobalTheory.HilbFam.LatticeUp
