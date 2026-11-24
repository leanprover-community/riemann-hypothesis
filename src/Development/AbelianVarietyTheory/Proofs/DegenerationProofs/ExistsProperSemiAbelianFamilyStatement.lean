module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProperSemiAbelianFamily
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_proper_semiAbelian_family' : ∀ (g n : ℕ), n.Prime → Odd n → ∃ a : ℕ, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R₀ : Subalgebra o Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) → ∀ (P : Out.PolAV (Sp Ω)) (ze : oˣ), P.g = g → IsUnit (n : o) → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → Nonempty (Out.Level P (n ^ a) (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) → ∃ (Z : Scheme.{0}) (s : Z ⟶ Sp o) (x : Sp Ω ⟶ Z) (G : Over Z) (_ : GrpObj G) (φ : P.A.left ⟶ G.left), IsProper s ∧ x ≫ s = spMap (algebraMap o Ω) ∧ IsSemiAbelian G ∧ IsGrpPullback P.A G x φ := by
  first | exact @GlobalTheory.exists_proper_semiAbelian_family | exact GlobalTheory.exists_proper_semiAbelian_family | (intros; apply GlobalTheory.exists_proper_semiAbelian_family <;> assumption)
