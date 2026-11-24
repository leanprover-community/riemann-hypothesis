module

public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalSeriesJacobianChainRuleLinearPart
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.formalSeriesJacobian_chain_rule_linearPart : ∀ (R : Type) [CommRing R] (d e : ℕ) (φ : Fin e → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∀ u : PS R 1 e, dl (sub ![φ] u) = (lin φ)ᵀ *ᵥ dl u ∧ MvPowerSeries.constantCoeff (sub ![φ] u) = MvPowerSeries.constantCoeff u) ∧ (∀ (m : ℕ) (ψ : Fin m → PS R 1 e), lin (fun j => sub ![φ] (ψ j)) = lin ψ * lin φ) ∧ ∀ (F : FGLaw R d) (F' : FGLaw R e), IsHomF F.F F'.F φ → ∀ u, IsCh F'.F u → IsCh F.F (sub ![φ] u) := by
  first | exact @GlobalTheory.ChF.chain_rule_lin | exact GlobalTheory.ChF.chain_rule_lin | (intros; apply GlobalTheory.ChF.chain_rule_lin <;> assumption)
