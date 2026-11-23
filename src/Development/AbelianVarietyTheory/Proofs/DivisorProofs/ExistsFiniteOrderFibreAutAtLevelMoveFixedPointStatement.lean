module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOrderFibreAutAtLevelMoveFixedPoint
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finiteOrder_fibreAut_at_levelMove_fixedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (x : Sp ℂ ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La), Formalism.L2.Pj.IsLevMove ρ ν gM gA → x ≫ ρ = x → ∃ (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N : ℕ) (ev : Dw.La → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), IsMonHom θ ∧ 0 < N ∧ (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A ∧ (∀ a, act.act a ≫ θ = θ ≫ act.act a) ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act.act c) ∧ (∀ a, ev a = 1 ↔ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, (∀ c ∈ l.Mb, q ≫ act.act c = 1) → ∃ a, ev a = q) ∧ ∀ a, ev (gM a) ≫ θ = ev a := by
  first | exact @GlobalTheory.LevMoveFibre.exists_fibreAut | exact GlobalTheory.LevMoveFibre.exists_fibreAut | (intros; apply GlobalTheory.LevMoveFibre.exists_fibreAut <;> assumption)
