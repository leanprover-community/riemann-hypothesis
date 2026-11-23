module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem _root_.GlobalTheory.HSApp.exists_dominant_sub {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    (la ν : _root_.GlobalTheory.AllWt.Weight Dw) (hla : _root_.GlobalTheory.HSApp.GapGe (1 : ℤ) la) :
    ∃ mu : _root_.GlobalTheory.AllWt.Weight Dw, _root_.GlobalTheory.HSApp.GapGe (0 : ℤ) mu ∧
      ∃ m : ℕ, 0 < m ∧ m • la - mu = ν := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ τ : _root_.GlobalTheory.AllWt.Psi H, ∀ k : ℕ,
      k + 1 < Dw.p + Dw.q → _root_.GlobalTheory.CompHS.gap (ν τ) k ≤ M := by
    refine ⟨Finset.univ.sup fun p : _root_.GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) =>
      (_root_.GlobalTheory.CompHS.gap (ν p.1) (p.2 : ℕ)).toNat, fun τ k hk => ?_⟩
    have h := Finset.le_sup (f := fun p : _root_.GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) =>
      (_root_.GlobalTheory.CompHS.gap (ν p.1) (p.2 : ℕ)).toNat)
      (Finset.mem_univ (τ, (⟨k, by omega⟩ : Fin (Dw.p + Dw.q))))
    exact (Int.self_le_toNat _).trans (by exact_mod_cast h)
  refine ⟨(M + 1) • la - ν, ?_, M + 1, Nat.succ_pos M, sub_sub_cancel _ _⟩
  unfold _root_.GlobalTheory.HSApp.GapGe at hla ⊢
  intro τ k hk
  have h₁ := hla τ k hk
  have h₂ := hM τ k hk
  unfold _root_.GlobalTheory.CompHS.gap at h₁ h₂ ⊢
  rw [dite_eq_left hk] at h₁ h₂ ⊢
  have e : ∀ i, ((M + 1) • la - ν) τ i = ((M + 1 : ℕ) : ℤ) * la τ i - ν τ i := by
    intro i
    simp
  rw [e, e]
  push_cast
  nlinarith

end GlobalTheory.HSApp
