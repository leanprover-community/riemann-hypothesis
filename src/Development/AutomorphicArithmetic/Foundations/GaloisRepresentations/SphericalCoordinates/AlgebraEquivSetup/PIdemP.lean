module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below finiteAdeleMap_apply)

theorem UpperTheory.Gal.W2.Seed.pIdemP :
    IdemP := by
  classical
  intro p _ E _ _
  let e : AfQ := ⟨fun v => if (p : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      by_cases h : (p : 𝓞 ℚ) ∈ v.asIdeal
      · simpa [h] using one_mem (v.adicCompletionIntegers ℚ)
      · simpa [h] using zero_mem (v.adicCompletionIntegers ℚ)⟩
  have he : ∀ v : Plc ℚ, e v = if (p : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0 := fun v => rfl
  refine ⟨e, fun v => ⟨fun h => by rw [he, if_pos h], fun h => by rw [he, if_neg h]⟩, fun w => ?_⟩
  have hiff : (p : 𝓞 ℚ) ∈ (below ℚ w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
    show (p : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) ↔ _
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  have hl : pLoc E w (finiteAdeleMap ℚ E e) =
      GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w (e (below ℚ w)) := rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hl, he, if_pos (hiff.2 h), map_one]
  · rw [hl, he, if_neg (fun h' => h (hiff.1 h')), map_zero]
