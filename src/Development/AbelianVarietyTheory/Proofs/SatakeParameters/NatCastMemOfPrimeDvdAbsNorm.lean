module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.KerTie

theorem natCast_mem_of_prime_dvd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {q : ℕ}
    (hq : q.Prime) (h : q ∣ Ideal.absNorm P.asIdeal) : (q : 𝓞 E) ∈ P.asIdeal := by
  have : Fact q.Prime := ⟨hq⟩
  have := P.isPrime
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) q h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : q • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  rw [nsmul_eq_mul] at h1
  have h2 : ((q : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

theorem sNum_qOf_rowSG :
    ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
      (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex),
      ∀ u μ (P : rowSG t.Pr t.sel (t.tup μ)), SNum (t.O u μ).S (qOf P.1) := by
  intro D L hT Gi Gl K Y cX ex t u μ P
  refine ⟨Nat.pos_of_ne_zero ?_, fun q hq hP => ?_⟩
  · simpa [Formalism.L2.Col.qOf, Ideal.absNorm_eq_zero_iff] using P.1.ne_bot
  rw [t.O_S]
  refine Finset.mem_insert_of_mem ?_
  rcases Finset.mem_union.1 P.2 with hG | hQ
  · refine Finset.mem_union_left _ ?_
    rcases Finset.mem_union.1 hG with h0 | h0
    · have e : Formalism.L2.Col.qOf P.1 = t.Pr.g 0 := t.pr_ok.vG_norm 0 P.1 h0
      rw [e] at hP
      rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 0)).1 hP, t.g_rec]
      simp
    · have e : Formalism.L2.Col.qOf P.1 = t.Pr.g 1 := t.pr_ok.vG_norm 1 P.1 h0
      rw [e] at hP
      rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 1)).1 hP, t.g_rec]
      simp
  · exact Finset.mem_union_right _
      ((t.Q_rec μ q).2 ⟨hq, P.1, hQ, natCast_mem_of_prime_dvd_absNorm P.1 hq hP⟩)

end GlobalTheory.KerTie
