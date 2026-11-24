module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesComplexEmbedd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Module NumberField

theorem _root_.GlobalTheory.T.embedsInRegularRepresentationCopies_complexEmbedding_indep : ∀ (K V V' G : Type) [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [Group G] [Finite G] (N : ℕ) (ρK : Representation K G (Fin N → K)) (σ σ' : K →+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (f : (Fin N → K) →ₛₗ[σ] V) (f' : (Fin N → K) →ₛₗ[σ'] V'), (LinearIndependent ℂ fun k => f (Pi.single k 1)) → Submodule.span ℂ (Set.range f) = ⊤ → (LinearIndependent ℂ fun k => f' (Pi.single k 1)) → Submodule.span ℂ (Set.range f') = ⊤ → (∀ g v, ρ g (f v) = f (ρK g v)) → (∀ g v, ρ' g (f' v) = f' (ρK g v)) → ∀ (H : Subgroup G) (n : ℕ), GlobalTheory.BadCount.EmbReg ρ H n → GlobalTheory.BadCount.EmbReg ρ' H n := by
  first | exact @GlobalTheory.BadCount.embReg_of_baseChange | exact GlobalTheory.BadCount.embReg_of_baseChange | (intros; apply GlobalTheory.BadCount.embReg_of_baseChange <;> assumption)
