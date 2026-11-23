module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasFDerivAtDerFamProdExp
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology


theorem _root_.GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  first | exact @GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp | exact GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp | (intros; apply GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp <;> assumption)
