module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveSpanMatrices
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.FundamentalSetFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting

@[expose] public section

namespace GlobalTheory.PoincareSeriesCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology
open GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames (GapsNonneg pairing IsInvWeight wsq normSq ATilde fundSq IsExt idFrame flagBall
  ballSup term PoincareStatement CuspidalStatement PoincareCuspidalStatement)
open scoped ENNReal NNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nonempty_type (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨_, not_not.mp (mt (X.cmType τ).mpr h)⟩⟩

theorem isOrth_x0F (X : Data E r) : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2

theorem not_isIso_of_definite (X : Data E r) (h : X.p0 = 0 ∨ X.p0 = r) (ξ : Fin r → E) :
    ¬ X.IsIso ξ := by
  rintro ⟨-, h0, hne⟩
  obtain ⟨τ⟩ := nonempty_type X
  have hx : X.IsOrtho (x0F X) := isOrth_x0F X
  have hdet : (mat (x0F X) τ).det ≠ 0 := (X.signature τ).choose_spec.1
  set y : Fin r → ℂ := Data.emb τ.1 ξ with hy
  have hyy : hermC τ.1 X.Gm y y = 0 := by rw [hy, hermC_emb, h0, map_zero]
  have hre := PositiveSpanMatrices.re_self X hx τ hdet y
  rw [hyy, Complex.zero_re] at hre
  have hsq : ∑ c : Fin r, ‖hermC τ.1 X.Gm y (col (mat (x0F X) τ) c)‖ ^ 2 = 0 := by
    rcases h with h | h
    · have hs : ∀ c : Fin r, sgn X.p0 (c : ℕ) = -1 := fun c => by simp [sgn, h]
      simp only [hs, neg_one_mul, Finset.sum_neg_distrib] at hre
      linarith
    · have hs : ∀ c : Fin r, sgn X.p0 (c : ℕ) = 1 := fun c => by simp [sgn, h, c.isLt]
      simp only [hs, one_mul] at hre
      linarith
  have hall : ∀ c, hermC τ.1 X.Gm y (col (mat (x0F X) τ) c) = 0 := by
    intro c
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ =>
      sq_nonneg ‖hermC τ.1 X.Gm y (col (mat (x0F X) τ) c)‖)).mp hsq c (Finset.mem_univ c)
    simpa using this
  have hy0 : y = 0 := by
    rw [PositiveSpanMatrices.expand X hx τ hdet y]
    simp [hall]
  apply hne
  funext a
  have : τ.1 (ξ a) = 0 := congrFun hy0 a
  exact (map_eq_zero τ.1).mp this

end

end GlobalTheory.PoincareSeriesCompare
