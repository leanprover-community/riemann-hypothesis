module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOneParameterSubgroupOfRationalFamily
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf

theorem _root_.GlobalTheory.T.exists_oneParameterSubgroup_of_rational_family : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (A : Type) [CommRing A] [Algebra k A] (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), SmConn G → IsChart G j ε f → Pd ≠ 0 → (∃ i, P i ≠ 0) → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → (∀ t t', t ≠ 0 → t' ≠ 0 → Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t * t') ≠ 0 → (algOverHom (ψ t) ≫ j) * (algOverHom (ψ t') ≫ j) = algOverHom (ψ (t * t')) ≫ j) → ∃ F : Gm (Sp k) ⟶ G, IsMonHom F ∧ F ≠ 1 := by
  first | exact @GlobalTheory.SS.ArcInf.exists_oneParameter_of_rational_family | exact GlobalTheory.SS.ArcInf.exists_oneParameter_of_rational_family | (intros; apply GlobalTheory.SS.ArcInf.exists_oneParameter_of_rational_family <;> assumption)
