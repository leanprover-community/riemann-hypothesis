module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero
public import Formalism.LocalToGlobal.CharacterGerms.IntSProd
public import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
public import Formalism.LocalToGlobal.CharacterGerms.SubstSubst
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem cc_smul {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hF, mul_zero]

theorem expS_copies (Y : FBChart C V O dd) (n : ℕ) :
    FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) =
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by
  have ha : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (![pt C dd b] s.1 s.2) = 0 := by
    intro b s
    simp [pt]
  have hc : ∀ b : Fin n, MvPowerSeries.constantCoeff (ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) = 0 := fun b =>
    (ordGE_one_iff _).1 (ordGE_subst (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))
      ((ordGE_one_iff _).2 (VP.cc_hL Y)))
  have hs : ∀ b : Fin n, ev (n := n) ![pt C dd b] ((Y.k : C) • Y.B.hL C Y.h Y.w0) =
      (Y.k : C) • ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0) := fun b =>
    MvPowerSeries.subst_smul (hasSubst_of_ordGE (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))) _ _

  rw [VP.expS_eq _ (cc_smul _ (by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hc b)), Finset.smul_sum,
  Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun b _ => cc_smul _ (hc b))]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [VP.expS_eq _ (cc_smul _ (VP.cc_hL Y))]
  show _ = MvPowerSeries.subst (fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (mvExp _)
  rw [VP.subst_exp (ha b) (cc_smul _ (VP.cc_hL Y))]
  exact congrArg mvExp (hs b).symm

theorem rowCopy_mul_exp {J : Fin 2 → Type} {n : ℕ} (b : Fin n) (F L : MvPowerSeries (WV J) C) :
    rowCopy b (F * mvExp L) = rowCopy b F * mvExp (rowCopy b L) := by
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq, rtj_rowCopy_eq, map_mul]
  congr 1
  ext x
  rw [MvPowerSeries.coeff_rename]
  show _ = ∑ k ∈ Finset.range (x.degree + 1),
    MvPowerSeries.coeff x ((MvPowerSeries.rename (rtjR b) L) ^ k) / (k.factorial : C)
  simp_rw [← map_pow, MvPowerSeries.coeff_rename, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hdeg : y.degree = x.degree := by
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage] at hy
    rw [← hy, Finsupp.degree_mapDomain]
  show ∑ k ∈ Finset.range (y.degree + 1), _ = _
  rw [hdeg]

end VP

end Formalism.L2.FormalSeriesBounds
