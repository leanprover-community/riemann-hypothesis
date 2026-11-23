module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.jetReading_linearSubstitution_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n n' m : ℕ) (B : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin n → Fin g → ℂ)) (sb : Fin n × Fin g → MvPolynomial (Fin n' × Fin g) ℂ), (∀ p, (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m) (psJet m (MvPowerSeries.X p)) = jetN m (fun w => B w p.1 p.2)) → ∀ (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.JetRd m φ ε τ Λ → Φ.JetRd m (fun k => spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m) ≫ φ k) ε (LB.pullGen L.L φ ε τ (spMap (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin n' × Fin g) m))) (fun k => Λ k ∘ₗ B) := by
  first | exact @GlobalTheory.JetLinSub.jetRd_linSubst | exact GlobalTheory.JetLinSub.jetRd_linSubst | (intros; apply GlobalTheory.JetLinSub.jetRd_linSubst <;> assumption)
