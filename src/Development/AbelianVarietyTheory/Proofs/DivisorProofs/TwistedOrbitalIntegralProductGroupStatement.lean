module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_productGroup : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G') (f : G → ℂ) (f' : G' → ℂ), (∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) → (∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) ≠ 0}.Finite → {q : DoubleCoset.Quotient (twCent θ' δ' : Set G') (K' : Set G') | ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * δ' * θ' (Quotient.out q * k)) ≠ 0}.Finite → twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  first | exact @GlobalTheory.BCT.OrbProd.twOrb_prod | exact GlobalTheory.BCT.OrbProd.twOrb_prod | (intros; apply GlobalTheory.BCT.OrbProd.twOrb_prod <;> assumption)
