module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.embedGL2_diag_mul_unipotent_theta_eq :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (x : A ℚ),
        em E (aE y) * gl (nU (D.mkE 0 x)) = nE D ![0, (y : A ℚ) * x] * em E (aE y) := by
  intro E _ _ D y x
  have hm : ∀ (h : GL (Fin 2) (A ℚ)) (i j : Fin 2), (em E h).val i j = AdeleBaseChange.adeleMap ℚ E (h.val i j) := fun _ _ _ => rfl
  have hn : ∀ (q : A E), (nU q).val = !![1, q; 0, 1] := fun _ => rfl
  have hk : ∀ u t : A ℚ, D.mkE u t = AdeleBaseChange.adeleMap ℚ E u + AdeleBaseChange.adeleMap ℚ E t * rt D.θ := fun _ _ => rfl
  refine Units.ext ?_
  ext i j
  simp only [nE, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hm]
  fin_cases i <;> fin_cases j <;> simp [aE, hn, hk, map_mul, mul_assoc]
