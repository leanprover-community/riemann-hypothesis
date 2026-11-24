module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousInsT
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PsiInnerSIns
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC mat_ext psiT_sigR finPart_sigR)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}


theorem compAt_sub_sIns {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ}
    (hdet : IsUnit fr.det) (y : Mx D m n) :
    (y - sIns τ fr (piF θ τ fr y)).map (psiT D τ) = 0 := by
  have hp : Matrix.of (piF θ τ fr y) = fr⁻¹ * compAt θ τ y := rfl
  rw [Matrix.map_sub (psiT D τ) (fun a b => map_sub (psiT D τ) a b), ← PlaceFactsH.compAt_eq_psiT hθ,
    ← PlaceFactsH.compAt_eq_psiT hθ, show sIns (D := D) τ fr (piF θ τ fr y) = insT τ (fr * Matrix.of (piF θ τ fr y)) from rfl,
    compAt_insT hθ, if_pos rfl, hp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, sub_self]



theorem inner_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} (x x' z : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D))
    (hz : z.map (psiT D τ) = 0) : inner V x z = inner V x' z := by
  apply mat_ext D
  · intro τ''
    rw [map_inner, map_inner]
    by_cases h : τ'' = τ
    · subst h; rw [hz, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero]
    · have := hx τ'' h
      rw [eq_thetaC D hθ] at this
      change x.map (psiT D τ'') = x'.map (psiT D τ'') at this
      rw [this]
  · have ha : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      simp only [adj, Matrix.map_apply, Matrix.transpose_apply, cA]
      rw [finPart_sigR, finPart_sigR]
      congr 1
      exact congrFun (congrFun hf j) i
    show (adj x * (gA V * z)).map (finPart D) = (adj x' * (gA V * z)).map (finPart D)
    rw [Matrix.map_mul, ha, ← Matrix.map_mul]

end PositivityTheory.Rg.Sw.Glob.FTH
