module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BaseChangeConj

open Formalism.MainNotions.SumRepresentations Polynomial

theorem charpoly_eq_of_dense' {Γ : Type} [Group Γ] [TopologicalSpace Γ] {k : Type} [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [Infinite k] {a : ℕ} (ρ₁ ρ₂ : Γ →* GL (Fin a) k)
    (h1 : Continuous fun g => ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h2 : Continuous fun g => ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (S : Set Γ) (hS : closure S = Set.univ)
    (hE : ∀ g ∈ S, ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) (g : Γ) :
    ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hc : IsClosed {g : Γ | (Matrix.scalar (Fin a) t - ((ρ₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det =
      (Matrix.scalar (Fin a) t - ((ρ₂ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).det} :=
    isClosed_eq (continuous_const.sub h1).matrix_det (continuous_const.sub h2).matrix_det
  have hsub : closure S ⊆ _ := hc.closure_subset_iff.mpr fun g hg => by
    show _ = _
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, hE g hg]
  rw [hS] at hsub
  exact hsub (Set.mem_univ g)

end GlobalTheory.BaseChangeConj
