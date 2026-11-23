module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelProjectiveGenericFibre
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.lie_model_projective_generic_fibre : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V] (MB : LieModel G z V) (T : Type) [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T] (TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T) (j : V →ₗ[𝓞 L] T) (U : Submodule Ω Li), IsCptGen ξ → (∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) → IsBaseChange L j → Module.finrank (𝓞 L) V = Module.finrank L T ∧ Module.finrank (𝓞 L) (FlagFib.subFib M U z MB) = Module.finrank L (Submodule.span L {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib | exact GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib <;> assumption)
