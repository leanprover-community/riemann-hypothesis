module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormFin
open GlobalTheory.AdelicU

theorem nnnorm_algebraMap_norm_le (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (y : E) :
    ‖algebraMap F (Fv F v) (Algebra.norm F y)‖₊ ≤
      absFin F v ((1 : Fv F v) ⊗ₜ[F] y) ^ Module.finrank F E := by
  rw [← absBar_algebraMap F v, ← IsScalarTower.algebraMap_apply,
    Algebra.norm_eq_prod_embeddings F (FvBar F v) y]
  rw [show absBar F v (∏ τ : E →ₐ[F] FvBar F v, τ y) = ∏ τ : E →ₐ[F] FvBar F v, absBar F v (τ y) from
    map_prod (valBar F v) _ _]
  rw [← AlgHom.card F E (FvBar F v), ← Finset.card_univ]
  refine Finset.prod_le_pow_card _ _ _ fun τ _ => ?_
  have := le_absFin F v τ ((1 : Fv F v) ⊗ₜ[F] y)
  simpa using this

theorem normFin_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : D.host.E) :
    ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F y)‖₊ ≤
      GlobalTheory.AdelicU.absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] y) ^ Module.finrank D.host.F D.host.E :=
  nnnorm_algebraMap_norm_le D.host.F v y

end GlobalTheory.NormFin
