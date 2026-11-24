module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamily
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem _root_.GlobalTheory.T.exists_scalar_heckeTrace_thetaGenerator_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i n : ℕ) (T : Type) [CommRing T] [IsReduced T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (s₀ : LB.Sec (PPx x')), admitted l P p → IsHeckeFam P p i Ψ → IsListed Ψ σ → SecGen x' s₀ → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁'), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → ∃ s', IsThGen x₁' s' ∧ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') → ∃ a : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → IsThGen x₁' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s' → SecBC χ.toRingHom a x' x₁' s₀ s' := by
  first | exact @GlobalTheory.HeckeScal.exists_scal_of_family | exact GlobalTheory.HeckeScal.exists_scal_of_family | (intros; apply GlobalTheory.HeckeScal.exists_scal_of_family <;> assumption)
