module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointAdelicRightMulLevel
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.chart_base_point_adelic_right_mul_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (κ : ((St i hi).K β).lev.U) (x x₁ : UA D i hi)
    (p q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (k : SB t μ → (Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i))),
    x₁.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → q.deco.1.N = p.deco.1.N → q.deco.1.f = p.deco.1.f →
    (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * k P) → (∀ P, k P ∈ GLint t.X.E (D.R.N i) P.1) →
    (∀ P, InFrame t.seam (A.fb i hi β) (t.cst μ).D P κ.1 (k P)) → IsPtAd A a i hi β x₁ q) := by
  first | exact @GlobalTheory.PtMove.isPtAd_mul_lev | exact GlobalTheory.PtMove.isPtAd_mul_lev | (intros; apply GlobalTheory.PtMove.isPtAd_mul_lev <;> assumption)
