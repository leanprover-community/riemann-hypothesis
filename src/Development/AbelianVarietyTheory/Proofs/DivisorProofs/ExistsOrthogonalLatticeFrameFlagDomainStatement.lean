module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomain
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_orthogonal_lattice_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ x ∈ X.dom, ∃ lam : Fin r → Fin r → E, (∀ j, lam j ∈ X.Λ) ∧ LinearIndependent E lam ∧ (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧ (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧ (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE X.p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE X.p0_le a))) := by
  first | exact @GlobalTheory.OrthoFrame.exists_orthoFrame | exact GlobalTheory.OrthoFrame.exists_orthoFrame | (intros; apply GlobalTheory.OrthoFrame.exists_orthoFrame <;> assumption)
