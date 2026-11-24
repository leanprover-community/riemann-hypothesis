module

public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBlockPolynomialGeProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.valuation_blockPolynomial_ge_prod : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Ty : Type) [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) (β : (Σ τ : Ty, Fin (r τ)) → Fin n), Function.Injective β → ∀ (a : Ty → ℕ → ℕ), Crude.Dom r a → ∀ (yv : Letter Ty r n → O) (x : Ty → NNReal), (∀ τ, x τ ≤ 1) → (∀ τ (i : Fin (r τ)), x τ ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => yv ⟨τ, Fin.castLE i.isLt a, β ⟨τ, Fin.castLE i.isLt b⟩⟩).det)) → (∏ τ, x τ ^ (a τ 0) ≤ v (algebraMap O C (MvPolynomial.eval yv (Crude.crP r n O β a)))) ∧ ∀ mo ∈ (Crude.crP r n O β a).support, ∀ ℓ, mo ℓ ≠ 0 → ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2 := by
  first | exact @GlobalTheory.CharDepth.valuation_blockPoly_ge | exact GlobalTheory.CharDepth.valuation_blockPoly_ge | (intros; apply GlobalTheory.CharDepth.valuation_blockPoly_ge <;> assumption)
