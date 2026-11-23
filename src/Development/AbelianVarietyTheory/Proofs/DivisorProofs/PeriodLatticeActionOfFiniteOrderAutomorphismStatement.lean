module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodLatticeActionOfFiniteOrderAutomorphism
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.periodLattice_action_of_finiteOrder_automorphism : ∀ (E : Type) [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) (θ : P.A ⟶ P.A) (N n : ℕ), IsMonHom θ → 0 < N → (fun f : P.A ⟶ P.A => f ≫ θ)^[N] (𝟙 P.A) = 𝟙 P.A → (∀ a, act.act a ≫ θ = θ ≫ act.act a) → 0 < n → ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (F : Λ →ₗ[𝓞 E] Λ) (ψ : Λ → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), Module.Finite (𝓞 E) Λ ∧ Module.IsTorsionFree (𝓞 E) Λ ∧ F ^ N = 1 ∧ (∀ a b, ψ (a + b) = ψ a * ψ b) ∧ (∀ (c : 𝓞 E) a, ψ (c • a) = ψ a ≫ act.act c) ∧ (∀ a, ψ a = 1 ↔ ∃ b, a = n • b) ∧ (∀ q : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, q ^ n = 1 → ∃ a, ψ a = q) ∧ ∀ a, ψ (F a) = ψ a ≫ θ := by
  first | exact @GlobalTheory.periodLattice_of_finiteOrder | exact GlobalTheory.periodLattice_of_finiteOrder | (intros; apply GlobalTheory.periodLattice_of_finiteOrder <;> assumption)
