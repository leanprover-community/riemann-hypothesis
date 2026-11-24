module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEvenRepsTensorLatticeAndSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.exists_even_reps_tensorLattice_and_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ N : ℕ, Odd N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∃ u : Fin ((⟨Λ⟩ : GenLat E n).zCard N r) → Matrix (Fin n) (Fin r) E, (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') ∧ (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') ∧ 0 < (⟨Λ⟩ : GenLat E n).zCard N r ∧ 0 < (⟨Λ⟩ : GenLat E n).mIdx N r ∧ ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∑ i, heisG X bas (u i) v = (((⟨Λ⟩ : GenLat E n).zCard N r : ℕ) : ℂ) • projA X bas w (tens Λ L) v := by
  first | exact @GlobalTheory.Dict.ZLat.exists_reps_sum | exact GlobalTheory.Dict.ZLat.exists_reps_sum | (intros; apply GlobalTheory.Dict.ZLat.exists_reps_sum <;> assumption)
