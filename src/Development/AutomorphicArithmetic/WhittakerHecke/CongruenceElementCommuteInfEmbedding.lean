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
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.congruence_element_commute_inf_embedding :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (M : ℕ) (κ : GL (Fin 2) (A E)), CongE M κ → ∀ X : GL (Fin 2) (Cinf E), κ * infGL E 2 X = infGL E 2 X * κ := by
  intro E _ _ _ M κ h X
  have h0 : ∀ c : A E, c.1 = 0 → pInf E c = 0 := fun c hc => by
    change (infEq E).symm c.1 = 0
    rw [hc]
    exact map_zero _
  have hk : GeneralLinearGroup.map (pInf E) κ = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    obtain ⟨⟨c, hc, e⟩, _⟩ := h i j
    have h1 := congrArg (pInf E) e
    rw [map_sub, map_mul, h0 c hc.1, mul_zero] at h1
    have h2 : pInf E (κ.val i j) = pInf E ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := sub_eq_zero.1 h1
    change pInf E (κ.val i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have e := infGL_mul_finGL κ
  rw [hk, map_one, one_mul] at e
  rw [← e]
  exact (infGL_comm X _).symm
