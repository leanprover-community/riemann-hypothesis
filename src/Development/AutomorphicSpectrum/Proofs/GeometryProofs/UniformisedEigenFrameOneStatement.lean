module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.uniformised_eigen_frame_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), LinearIndependent (𝓞 E) e → IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → ∃! x : (Fin D.p → Fin g → ℂ) × (Fin D.q → Fin g → ℂ) × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ × ℂ, (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.1 a) (v a).left) ∧ (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (x.2.1 j) (w j).left) ∧ (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, x.2.2.2.1 j n • x.2.1 j) ∧ (∀ j n, ∑ m, x.2.2.1 j m * τ' (sesq (FU.Di i) (e m) (e n)) = x.2.2.2.1 j n) ∧ x.2.2.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, ∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) ∧ ∀ C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ, (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = x.1 a) → (Matrix.fromRows C x.2.2.1).det = x.2.2.2.2 := by
  exact @GlobalTheory.CompanionTheory.Ar.Flat.anSolve
