module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.unipotentTheta_mem_congruence_of_integral :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (M d : ℕ), (∀ w : H.P E, Valued.v (H.cp w (rt ((d : E) * D.θ))) ≤ 1) → ∀ c ∈ Oh ℚ, CongE M (nu D ((M : A ℚ) * (d : A ℚ) * c)) := by
  intro E _ _ D M d hd c hc
  have hk : ∀ u t : A ℚ, D.mkE u t = AdeleBaseChange.adeleMap ℚ E u + AdeleBaseChange.adeleMap ℚ E t * rt D.θ := fun _ _ => rfl
  have h0 : (0 : A E) ∈ Oh E := ⟨rfl, fun w => by
    change Valued.v (0 : H.Kv w) ≤ 1
    simp⟩
  have hneg : ∀ s : A E, s ∈ Oh E → -s ∈ Oh E := fun s hs => ⟨by
    change -s.1 = 0
    rw [hs.1, neg_zero], fun w => by
    have e : (-s).2 w = -(s.2 w) := rfl
    rw [e, Valuation.map_neg]
    exact hs.2 w⟩
  have hfst : (AdeleBaseChange.adeleMap ℚ E c).1 = 0 := by
    obtain ⟨c1, c2⟩ := c
    obtain rfl : c1 = 0 := hc.1
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have hb : AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ) ∈ Oh E := by
    refine ⟨?_, fun w => ?_⟩
    · change (AdeleBaseChange.adeleMap ℚ E c).1 * _ = 0
      rw [hfst, zero_mul]
    · have h1 : Valued.v ((AdeleBaseChange.adeleMap ℚ E c).2 w) ≤ 1 :=
        GroundTheory.Global.AdeleBaseChange.mapsTo_completionMap _ w (hc.2 _)
      have e : (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)).2 w =
          (AdeleBaseChange.adeleMap ℚ E c).2 w * H.cp w (rt ((d : E) * D.θ)) := rfl
      rw [e, map_mul]
      exact mul_le_one' h1 (hd w)
  have hx : D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c) = (M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)) := by
    have hr : rt ((d : E) * D.θ) = (d : A E) * rt D.θ := by
      change algebraMap E (A E) ((d : E) * D.θ) = _
      rw [map_mul, map_natCast]
    rw [hk, map_zero, zero_add, map_mul, map_mul, map_natCast, map_natCast, hr]
    ring
  have key : ∀ s : A E, s ∈ Oh E → ∀ i j, ∃ c ∈ Oh E,
      (!![1, (M : A E) * s; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (M : A E) * c := by
    intro s hs i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, h0, by simp⟩
    · exact ⟨s, hs, by simp⟩
    · exact ⟨0, h0, by simp⟩
    · exact ⟨0, h0, by simp⟩
  have hinv : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := by
    intro q
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    change (!![1, q; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) * !![1, -q; 0, 1] = 1
    simp [Matrix.mul_fin_two, Matrix.one_fin_two]
  have hn : nu D ((M : A ℚ) * (d : A ℚ) * c) = gl (nU ((M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)))) := by
    change gl (nU (D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c))) = _
    rw [hx]
  intro i j
  rw [hn, hinv, ← mul_neg]
  exact ⟨key _ hb i j, key _ (hneg _ hb) i j⟩
