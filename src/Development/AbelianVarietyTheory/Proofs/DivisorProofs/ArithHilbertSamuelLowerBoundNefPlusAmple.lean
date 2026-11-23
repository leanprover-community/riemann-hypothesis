module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedModelDominantCurveRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPosStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundAlongResidues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lowerBound_along_div : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c n : ℕ) (α : ℝ), 0 < n → NefFib P.L → P.L.SemiPos D → IsAmpleLB P.A.B → P.A.SemiPos D → ((P.L.pow n).tens P.A).IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (α / (D + 1).factorial / (n : ℝ) ^ (D + 1) - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M ((M / n : ℕ) - c) 1 := by
  intro _ hHS k _ X _ p D hX P c n α hn hL hLs hA hAs hα ε hε
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  have hLn : NefFib (P.L.pow n) := fun Z i _ _ κ _ _ _ hd => by
    rw [NefHodgeTateAt.topSelf_pow hp P.L n Z i κ hd]
    exact mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)
  have hAmp : IsAmpleLB ((P.L.pow n).tens P.A).B := GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX _ _ hLn hA
  have hSP : ((P.L.pow n).tens P.A).SemiPos D := (hLs.pow n).tens hAs
  have hRep : P.Rep (n : ℤ) 1 ((P.L.pow n).tens P.A) := by
    have h1 := Pair.rep_pow k X p P 1 0 P.L n (Pair.rep_base k X p P).1
    have h2 := Pair.rep_tens k X p P _ _ 0 1 _ _ h1 (Pair.rep_base k X p P).2.1
    simpa using h2
  refine lowerBound_along_residues (D + 1) n (fun M => P.lc M ((M / n : ℕ) - c) 1) (α / (D + 1).factorial) hn
    (fun r hr ε' hε' => ?_) ε hε
  filter_upwards [GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos hHS k X p D hX P n 1 r (-(c : ℤ)) _ α hRep hAmp hSP hα ε' hε'] with q hq
  have e : (n * q + r) / n = q := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hr, zero_add]
  simp only [e]
  convert hq using 2 <;> push_cast <;> ring

end GlobalTheory.HSNef
