module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianPullbackTorusExtension
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.semi_abelian_pullback_torus_extension : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) (G' : Over (Sp (𝓞 L))) [GrpObj G'] (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → IsGrpPullback τ.B G' (spMap (algebraMap (𝓞 L) L)) φ' → ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (V V' : Type) [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup V'] [Module (𝓞 L) V'] (M : LieModel G z V) (M' : LieModel G' (𝟙 _) V') (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∃ (ε : Fin r → V) (f : V →ₗ[𝓞 L] V'), (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt (ε a)).left)) ∧ (∀ (e : V) (v : epsAt (𝟙 (Sp L)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M'.pt (f e)).left)) ∧ LinearIndependent (𝓞 L) ε ∧ LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε) ∧ ∀ e' : V', ∃ (a : 𝓞 L) (e : V), a ≠ 0 ∧ f e = a • e' := by
  exact @GlobalTheory.CompanionTheory.Ar.TopPt.main
