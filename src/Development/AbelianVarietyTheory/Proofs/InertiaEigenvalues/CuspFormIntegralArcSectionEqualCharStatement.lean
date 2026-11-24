module

public import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralArcSectionEqualChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.GoodTransfer

theorem _root_.GlobalTheory.T.cuspForm_integral_arc_section_equalChar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype), PushInvertible Y.t.G Y.t.PP.L → IsOpen (abLocus Y.t.G) → Y.N4 → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a' n → f ∈ cusp Xo c U a' n → (∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ k : c.F, io₁ k ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ y₁ : IntFr Xo c T₁ io₁, (letI := io₁.toAlgebra; ExtIn Y (abLocus Y.t.G) T₁ io₁ y₁.1.x) → evI y₁ f ∈ (algebraMap T₁.V T₁.Fr).range) → ∀ (T : CDVR) (io : c.F →+* T.Fr), (∀ k : c.F, io k ∈ (algebraMap T.V T.Fr).range) → (∃ κ : T.Fr →+* ℂ, κ.comp io = c.F.val.toRingHom) → ∀ (b : (la.valuation c.F).valuationSubring →+* T.V), (algebraMap T.V T.Fr).comp b = io.comp (la.valuation c.F).valuationSubring.subtype → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (a : ArcIn Dw l (la.valuation c.F).valuationSubring.subtype T.V b) (y' : Sp T.V ⟶ Y.X), y' ≫ Y.s = spMap b → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y' → ∀ (y : IntFr Xo c T io) (z : Sp T.Fr ⟶ Xo.XF c), (letI := io.toAlgebra; z ≫ pullback.fst _ _ = y.1.x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → evI y f ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | exact GlobalTheory.GoodTransfer.inV_of_arc_of_extIn | (intros; apply GlobalTheory.GoodTransfer.inV_of_arc_of_extIn <;> assumption)
