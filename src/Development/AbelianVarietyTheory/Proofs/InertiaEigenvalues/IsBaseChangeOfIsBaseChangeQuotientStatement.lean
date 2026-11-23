module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Jacobson.Ideal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeOfIsBaseChangeQuotient
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isBaseChange_of_isBaseChange_quotient_comp : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (𝔞 : Ideal S), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] (V : Type) [AddCommGroup V] [Module S V] [Module R V] [IsScalarTower R S V] [Module.Finite S V] [Module.Projective S V] (W : Type) [AddCommGroup W] [Module (S ⧸ 𝔞) W] [Module S W] [Module R W] [IsScalarTower S (S ⧸ 𝔞) W] [IsScalarTower R (S ⧸ 𝔞) W] [IsScalarTower R S W] (u : P →ₗ[R] V) (g : V →ₗ[S] W), IsBaseChange (S ⧸ 𝔞) g → IsBaseChange (S ⧸ 𝔞) (g.restrictScalars R ∘ₗ u) → IsBaseChange S u := by
  first | exact @GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient | exact GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient | (intros; apply GlobalTheory.BSP.isBaseChange_of_isBaseChange_quotient <;> assumption)
