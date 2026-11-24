module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualAndPrincipalCongruenceOrbitsOfGoodLevel
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.selfDual_and_principalCongruence_orbits_of_goodLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ γ' ∧ (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧ ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  first | exact @GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | exact GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | (intros; apply GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf <;> assumption)
