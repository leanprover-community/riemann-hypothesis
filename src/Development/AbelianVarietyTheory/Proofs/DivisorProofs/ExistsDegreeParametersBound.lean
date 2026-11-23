module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.HSShortRun

open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) : Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dite_eq_right hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt_of_wtBig {P : WtPar Dw} (h : WtBig P) : ∀ i, GapGe (FlagTan.dimFlag Dw + 1) (P.wt i) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  intro i τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg i) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

end Weights

variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}


end GlobalTheory.HSShortRun
