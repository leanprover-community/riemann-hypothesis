module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureSectionRatiosGenerateFunctions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.pureSection_ratios_generate_functions : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (I : Type) (e : Module.Basis I ℤ Φ.E.X) (φ₀ : (Φ.H 1).Sec) (V : Φ.E.B.left.Opens), IsAffineOpen V → Φ.Pure 0 φ₀ → Φ.D.q.left ⁻¹ᵁ V ≤ Out.nonzeroLocus φ₀ → (∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ R : Subring Γ(Φ.G.left, Φ.D.q.left ⁻¹ᵁ V), (∀ a, (Φ.D.q.left.app V).hom a ∈ R) → (∀ i (φ : (Φ.H 1).Sec) r, (Φ.Pure (e i) φ ∨ Φ.Pure (-e i) φ) → IsRatio φ φ₀ _ r → r ∈ R) → R = ⊤) := by
  first | exact @GlobalTheory.ZH.WtGen.ratios_generate | exact GlobalTheory.ZH.WtGen.ratios_generate | (intros; apply GlobalTheory.ZH.WtGen.ratios_generate <;> assumption)
