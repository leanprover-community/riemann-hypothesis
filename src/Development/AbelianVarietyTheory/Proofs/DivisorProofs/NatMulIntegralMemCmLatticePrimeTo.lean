module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorPrimeToLFiniteAdele
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
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

namespace GlobalTheory.HilbFam.LatDen

theorem nat_mul_integral_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) (c : Ideal (OF E)) (y : (Af E)ˣ) (R : ℕ), l.Prime → OneOver l y → 0 < R → (R : OF E) ∈ c → ∃ M : ℕ, ¬ l ∣ M ∧ ∀ x : E, IsIntegral ℤ x → ((M * R : ℕ) : E) * x ∈ lattice c y := by
  intro E _ _ l c y R hl hy hR hRc
  obtain ⟨M, hM, hMz⟩ := GlobalTheory.HilbFam.AdeleDen.exists_den_prime_to E l ((y⁻¹ : (Af E)ˣ) : Af E) hl (fun w hw => by
    have h1 : ((y⁻¹ : (Af E)ˣ) : Af E) w * (y : Af E) w = 1 := by
      have h := congrArg (fun a : Af E => a w) (Units.inv_mul y)
      exact h
    rw [hy w hw, mul_one] at h1
    rw [h1, map_one])
  refine ⟨M, hM, fun x hx => ?_⟩
  show algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c
  refine GlobalTheory.CMVal.LatEnt.mem_hatO_of_sub hR hRc (zero_mem _) fun P => ?_
  have e : (algebraMap E (Af E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E)) P - (0 : Af E) P =
      (R : P.adicCompletion E) * (algebraMap E (P.adicCompletion E) x *
        (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P) := by
    rw [show (0 : Af E) P = 0 from rfl, sub_zero,
      show (algebraMap E (Af E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E)) P =
        algebraMap E (P.adicCompletion E) (M : E) * ((y⁻¹ : (Af E)ˣ) : Af E) P from rfl]
    show algebraMap E (P.adicCompletion E) (((M * R : ℕ) : E) * x) * ((y⁻¹ : (Af E)ˣ) : Af E) P = _
    rw [map_mul, map_natCast, map_natCast]
    push_cast
    ring
  have hx1 : Valued.v (algebraMap E (P.adicCompletion E) x) ≤ 1 := by
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P]
      rfl
    rw [h2]
    have : x = algebraMap (𝓞 E) E ⟨x, hx⟩ := rfl
    rw [this]
    exact P.valuation_le_one _
  rw [e, map_mul, GlobalTheory.CMVal.LatEnt.radN, map_mul]
  exact mul_le_of_le_one_right' (mul_le_one' hx1 (hMz P))

end GlobalTheory.HilbFam.LatDen
