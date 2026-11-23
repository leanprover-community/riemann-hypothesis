module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecomposition
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.isotropic_group_primary_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x z → ∃ (J J' : Type) (_ : Fintype J) (_ : Fintype J') (a : J → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (a' : J' → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (σ : J × J' ≃ Fin (Λ.zCard N (Dw.p + Dw.q))), Function.Injective a ∧ (∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) ∧ (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ i b, a' i b ^ m = 1 ∧ a' i b ^ (N ^ 2) = 1) ∧ (∀ i i' b, z (σ (i, i')) b = a i b * a' i' b) ∧ Fintype.card J = ℓ ^ (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ := by
  first | exact @GlobalTheory.isotropic_primary_decomposition | exact GlobalTheory.isotropic_primary_decomposition | (intros; apply GlobalTheory.isotropic_primary_decomposition <;> assumption)
