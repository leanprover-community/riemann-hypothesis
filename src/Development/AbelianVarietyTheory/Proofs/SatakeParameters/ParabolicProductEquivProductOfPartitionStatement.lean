module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil


theorem _root_.GlobalTheory.T.parabolicProduct_equiv_product_of_partition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)) (r t : ℕ) (e : (Σ a, Fin (d a)) ≃ Fin (r + t)) (e₁ : (Σ a : Fin Sᶜ.card, Fin (d (Sᶜ.orderEmbOfFin rfl a))) ≃ Fin r) (e₂ : (Σ b : Fin S.card, Fin (d (S.orderEmbOfFin rfl b))) ≃ Fin t), (∀ a b, a ∉ S → b ∈ S → ∀ (n : Type) [Fintype n] [DecidableEq n] (f : (Σ i : Fin 2, Fin (d (![a, b] i))) ≃ n) (f' : (Σ i : Fin 2, Fin (d (![a, b] (Equiv.swap 0 1 i)))) ≃ n), Nonempty ((multiProd f fun i => (σ (![a, b] i)).π).Equiv (multiProd f' fun i => (σ (![a, b] (Equiv.swap 0 1 i))).π))) → Nonempty ((multiProd e fun a => (σ a).π).Equiv (prod₂ (multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π) (multiProd e₂ fun b => (σ (S.orderEmbOfFin rfl b)).π))) := by
  first | exact @GlobalTheory.ProdReorder.reorder_split | exact GlobalTheory.ProdReorder.reorder_split | (intros; apply GlobalTheory.ProdReorder.reorder_split <;> assumption)
