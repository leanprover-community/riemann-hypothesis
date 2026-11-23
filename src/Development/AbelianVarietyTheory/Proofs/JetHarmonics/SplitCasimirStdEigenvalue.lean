module

public import Formalism.RealPlaceAnalysis.StatementE
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixLastRowInvertsCasimirStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorStdRelAdjointSplitCasimir
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

open Formalism.REAL

namespace GlobalTheory

theorem splitCasimirStd_eigenvalue : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + 0 := by
  intro V _ _ _ n E Et Om m hE hadj hq hEt hOm lam x hx hlam
  obtain ⟨K, hK, -⟩ := GlobalTheory.T.capelli_comatrix_last_row_inverts_casimir V n E Om m hE hq hOm
  obtain ⟨-, -, -, hc⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hE hadj hEt hOm
  by_contra hne
  have hprod : (∏ j, (-lam + m j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun j _ h => hne ⟨j, ?_⟩
    linear_combination -h
  have hlast : ∀ y, Om y = lam • y → y (Fin.last n) = 0 := by
    intro y hy
    have h := hK (-lam) y
    rw [hy, sub_zero, neg_smul, neg_add_cancel, map_zero] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hprod
  apply hx
  refine PiLp.ext fun c => ?_
  have h1 : Om (Et (Fin.last n) c x) = lam • Et (Fin.last n) c x := by
    have h := LinearMap.congr_fun (hc (Fin.last n) c) x
    simp only [Module.End.mul_apply] at h
    rw [h, hlam, map_smul]
  have h2 := hlast _ h1
  rw [hEt, hlast x hlam] at h2
  simpa using h2

end GlobalTheory
