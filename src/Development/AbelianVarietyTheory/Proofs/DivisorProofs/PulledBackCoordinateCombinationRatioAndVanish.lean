module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.PullCoordComb

def evalF {X : Scheme.{0}} (L : LB X) (i : L.ι) : LB.Sec L →+ Γ(X, L.U i) where
  toFun s := s.f i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem sum_smul_f {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : Fin n → Γ(X, ⊤)) (s : Fin n → LB.Sec L)
    (i : L.ι) : (∑ k, a k • s k).f i = ∑ k, resG X le_top (a k) * (s k).f i := by
  change evalF L i (∑ k, a k • s k) = _

  rw [map_sum]
  rfl

theorem linComb_ratio_and_vanish : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    (∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    (∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
          ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i)) ∧
    (y ≠ 0 → ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, algebraMap K Ω (lam k : K) * y k = 0 →
        ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) := by
  intro K Ω _ _ _ _ m y X _ p g ψ hbase hratio
  have hA : ∀ (lam : Fin (m + 1) → 𝓞 K) (l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι)
      (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
      ψ (y l) * fnOf _ h ((∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i) =
        ψ (∑ k, algebraMap K Ω (lam k : K) * y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) := by
    intro lam l i h

    rw [sum_smul_f, map_sum, Finset.mul_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, fnOf_resG, ← hbase, map_mul, mul_left_comm (ψ (y l)), hratio l k i h]
    ring
  refine ⟨hA, fun hy lam hsum => ?_⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, y k₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (funext hc)
  apply GlobalTheory.LB.f_injective
  funext i
  apply GlobalTheory.Cartier.fn_ext
  intro hU
  have e := hA lam k₀ i hU
  rw [hsum, map_zero, zero_mul] at e
  have hψ : ψ (y k₀) ≠ 0 := (map_ne_zero ψ).2 hk₀
  rw [GlobalTheory.LB.zero_f, map_zero]
  exact (mul_eq_zero.1 e).resolve_left hψ

end GlobalTheory.PullCoordComb
