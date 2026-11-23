module

public import Development.EtaleCohomology.TateTwists.EtaleSimplexSubfaceComposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SubdivisionComposition

lemma subint_comp (N j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l) :
    SimplexCategory.subinterval j' l' h' ≫ SimplexCategory.subinterval j l h =
      SimplexCategory.subinterval (n := N) (j + j') l' (by omega) := by
  ext i
  change ((i : ℕ) + j' + j) = (i : ℕ) + (j + j')
  omega

lemma subint_id (N : ℕ) :
    SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ := by
  ext i
  simp [SimplexCategory.subinterval]

lemma along_comp {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) :
    (x.along a).along b = x.along (b ≫ a) := by
  simp only [Sx.along, op_comp, Functor.map_comp, NatTrans.comp_app, types_comp_apply]

end LateralTheory.EtaleFoundations.SubdivisionComposition

open LateralTheory.EtaleFoundations.SubdivisionComposition in
theorem LateralTheory.EtaleFoundations.simplicial_subinterval_of_subinterval_along_etale : LateralTheory.EtaleFoundations.EtaleSimplexSubfaceComposition := by
  intro E U N x
  have hsa : ∀ (j l : ℕ) (h : j + l ≤ N), x.sub j l h = x.along (SimplexCategory.subinterval j l h) :=
    fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    change (x.along _).along _ = x.along _
    rw [along_comp, subint_comp]
  · rw [hsa, subint_id]
    simp [Sx.along]
  · intro j l h
    refine ⟨?_, ?_, hsa j l h⟩
    · intro V g
      simp only [Sx.sub, Sx.res]
      have hn := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
      simp only [ConcreteCategory.comp_apply] at hn
      exact hn
    · intro E' f
      simp only [Sx.sub, Sx.map]
      have hn := congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)
      simp only [NatTrans.comp_app] at hn
      first
        | (have hm := ConcreteCategory.congr_hom hn x
           simp only [ConcreteCategory.comp_apply] at hm
           first | exact hm | exact hm.symm)
        | exact (congrFun hn x).symm
        | (rw [← types_comp_apply, ← hn]; rfl)
  · intro p r a b
    exact along_comp x a b
