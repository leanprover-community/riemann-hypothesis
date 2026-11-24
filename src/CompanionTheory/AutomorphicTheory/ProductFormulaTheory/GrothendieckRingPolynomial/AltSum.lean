module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltComb, CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum

-- ===== clump member: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltComb =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltComb", "h": "module\n\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltComb\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.BitVec\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Zc.Cos

namespace CompanionTheory.Groth.AltC

theorem filter_mem_eq_of_sublist {α : Type*} [DecidableEq α] {l m : List α} (hs : l.Sublist m)
    (hm : m.Nodup) : m.filter (fun x => decide (x ∈ l)) = l := by
  apply PositivityTheory.Groth.AltC.filter_mem_eq_of_sublist <;> assumption

theorem mem_sub {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) (x : α) :
    x ∈ sub W c i ↔ ∃ p, c p = i ∧ W.get p = x := by
  apply PositivityTheory.Groth.AltC.mem_sub

theorem mem_sub_self {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (p : Fin W.length) :
    W.get p ∈ sub W c (c p) := by
  apply PositivityTheory.Groth.AltC.mem_sub_self

theorem sub_sublist {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    (sub W c i).Sublist W := by
  apply PositivityTheory.Groth.AltC.sub_sublist


open Classical in
theorem shuffleCount_eq {α : Type*} {h : ℕ} (W : List α) (D : Fin h → List α) (hW : W.Nodup) :
    shuffleCount W D = if (∀ i, (D i).Sublist W) ∧ (∀ x ∈ W, ∃! i, x ∈ D i) then 1 else 0 := by
  apply PositivityTheory.Groth.AltC.shuffleCount_eq <;> assumption

theorem cond_map {β α : Type*} {h : ℕ} (f : β → α) (hf : Function.Injective f) (w : List β)
    (E : Fin h → List β) :
    ((∀ i, ((E i).map f).Sublist (w.map f)) ∧ (∀ x ∈ w.map f, ∃! i, x ∈ (E i).map f)) ↔
      ((∀ i, (E i).Sublist w) ∧ (∀ y ∈ w, ∃! i, y ∈ E i)) := by
  apply PositivityTheory.Groth.AltC.cond_map <;> assumption

def wN (L : ℕ) (T : Finset ℕ) : List ℕ :=
  ((List.range L).filter (fun x => decide (x ∈ T))).reverse ++ (List.range L).filter (fun x => decide (x ∉ T))

theorem mem_wN {L x : ℕ} {T : Finset ℕ} : x ∈ wN L T ↔ x < L := by
  apply PositivityTheory.Groth.AltC.mem_wN

theorem nodup_wN (L : ℕ) (T : Finset ℕ) : (wN L T).Nodup := by
  apply PositivityTheory.Groth.AltC.nodup_wN

theorem sublist_of_lt {l m : List ℕ} (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·))
    (hs : ∀ x ∈ l, x ∈ m) : l.Sublist m := by
  apply PositivityTheory.Groth.AltC.sublist_of_lt <;> assumption

theorem run_sublist {L b l : ℕ} {T : Finset ℕ} (hbl : b + l ≤ L) :
    ((List.range' b l).reverse).Sublist (wN L T) ↔ ∀ x, b < x → x < b + l → x ∈ T := by
  apply PositivityTheory.Groth.AltC.run_sublist <;> assumption

def Cond (L : ℕ) (T : Finset ℕ) {h : ℕ} (b l : Fin h → ℕ) : Prop :=
  (∀ i, ((List.range' (b i) (l i)).reverse).Sublist (wN L T)) ∧
    (∀ x ∈ wN L T, ∃! i, x ∈ (List.range' (b i) (l i)).reverse)

theorem cond_iff {L : ℕ} {T : Finset ℕ} {h : ℕ} {b l : Fin h → ℕ} (hl : ∀ i, 0 < l i) :
    Cond L T b l ↔ (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧
      (∀ i x, b i < x → x < b i + l i → x ∈ T) := by
  apply PositivityTheory.Groth.AltC.cond_iff <;> assumption

end CompanionTheory.Groth.AltC

namespace CompanionTheory.Groth.AltC


open Classical in
theorem altSumN (L : ℕ) (hL : 0 < L) (s : Finset (Finset (Fin L))) (hs : ∀ S, S ∈ s ↔ ∀ a ∈ S, (a : ℕ) ≠ 0)
    {h : ℕ} (b l : Fin h → ℕ) (hl : ∀ i, 0 < l i) (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, f S = (-1) ^ S.card * if Cond L (S.map Fin.valEmbedding) b l then 1 else 0) :
    ∑ S ∈ s, f S = if h = 1 ∧ ∀ i, b i = 0 ∧ l i = L then (-1) ^ (L - 1) else 0 := by
  apply PositivityTheory.Groth.AltC.altSumN <;> assumption

end CompanionTheory.Groth.AltC

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltComb =====

-- ===== clump member: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum =====
-- clump-header: {"m": "CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltComb\npublic import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace CompanionTheory.Groth.AltS

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tN (Δ : Segment k) (n : ℕ) : IrrGL (k := k) := Δ.first.nu (n : ℂ)

theorem tN_injective (Δ : Segment k) : Function.Injective (tN Δ) := fun a b h =>
  _root_.GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ.first Δ.isCusp_first a b h

theorem tN_zero (Δ : Segment k) : tN Δ 0 = Δ.first := by
  simp [tN]

theorem vWord_eq (Δ : Segment k) (S : Finset (Fin Δ.len)) :
    vWord Δ S = (AltC.wN Δ.len (S.map Fin.valEmbedding)).map (tN Δ) := by
  have key : ∀ (p : Fin Δ.len → Bool) (q : ℕ → Bool), (∀ a : Fin Δ.len, p a = q a) →
      ((List.finRange Δ.len).filter p).map Fin.val = (List.range Δ.len).filter q := by
    intro p q hpq
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    congr 1
    exact List.filter_congr fun a _ => hpq a
  have hmemS : ∀ a : Fin Δ.len, (a : ℕ) ∈ S.map Fin.valEmbedding ↔ a ∈ S := fun a => Finset.mem_map' Fin.valEmbedding
  unfold vWord AltC.wN
  rw [← key (fun a => decide (a ∈ S)) (fun n => decide (n ∈ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← key (fun a => decide (a ∉ S)) (fun n => decide (n ∉ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← List.map_reverse, ← List.map_append, List.map_map]
  rfl

theorem decWord_eq (Δ Γ : Segment k) (b : ℕ) (hb : Γ.first = tN Δ b) :
    decWord Γ = ((List.range' b Γ.len).reverse).map (tN Δ) := by
  unfold decWord
  rw [List.map_reverse]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
  rw [Segment.term, hb, tN, tN]
  simp [Nat.cast_add]

theorem first_mem_decWord (Γ : Segment k) : Γ.first ∈ decWord Γ := by
  unfold decWord
  rw [List.mem_reverse, List.mem_ofFn]
  exact ⟨⟨0, Γ.len_pos⟩, by simp [Segment.term]⟩

end CompanionTheory.Groth.AltS

namespace CompanionTheory.Groth

open AltS

theorem altSum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    AltSum k := by
  intro Δ h Γ
  have hW : ∀ S, (vWord Δ S).Nodup := fun S => by
    rw [vWord_eq]; exact (AltC.nodup_wN _ _).map (tN_injective Δ)
  have hmapiff : (Finset.univ.val.map Γ = {Δ}) ↔ h = 1 ∧ ∀ i, Γ i = Δ := by
    rw [← Multiset.replicate_one, Multiset.eq_replicate]
    simp
  by_cases hex : ∀ i, ∃ n, (Γ i).first = tN Δ n
  · choose b hb using hex
    have hd : ∀ i, decWord (Γ i) = ((List.range' (b i) (Γ i).len).reverse).map (tN Δ) :=
      fun i => decWord_eq Δ (Γ i) (b i) (hb i)
    have H := AltC.altSumN Δ.len Δ.len_pos (vSets Δ) (by intro S; simp [vSets]) b (fun i => (Γ i).len)
      (fun i => (Γ i).len_pos)
      (fun S => (-1 : ℤ) ^ S.card * (shuffleCount (vWord Δ S) (fun i => decWord (Γ i)) : ℤ)) (by
        intro S
        congr 1
        rw [AltC.shuffleCount_eq _ _ (hW S)]
        have e : ((∀ i, (decWord (Γ i)).Sublist (vWord Δ S)) ∧ ∀ x ∈ vWord Δ S, ∃! i, x ∈ decWord (Γ i)) ↔
            AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len) := by
          simp only [hd, vWord_eq]
          rw [AltC.cond_map (tN Δ) (tN_injective Δ)]
          rfl
        by_cases hC : AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len)
        · rw [if_pos (e.2 hC), if_pos hC]; simp
        · rw [if_neg (mt e.1 hC), if_neg hC]; simp)
    rw [H]
    have hiff : (h = 1 ∧ ∀ i, b i = 0 ∧ (Γ i).len = Δ.len) ↔ Finset.univ.val.map Γ = {Δ} := by
      rw [hmapiff]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun ⟨h0, hl⟩ => ?_, fun he => ⟨?_, by rw [he]⟩⟩
      · exact Segment.ext_first (by rw [hb i, h0, tN_zero]) hl
      · exact tN_injective Δ (by rw [← hb i, he, tN_zero])
    by_cases hc : Finset.univ.val.map Γ = {Δ}
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (mt hiff.1 hc), if_neg hc]
  · push Not at hex
    obtain ⟨i, hi⟩ := hex
    rw [if_neg]
    · apply Finset.sum_eq_zero
      intro S _
      rw [AltC.shuffleCount_eq _ _ (hW S), if_neg]
      · simp
      rintro ⟨hs, _⟩
      have := (hs i).subset (first_mem_decWord (Γ i))
      rw [vWord_eq, List.mem_map] at this
      obtain ⟨n, _, hn⟩ := this
      exact hi n hn.symm
    · rw [hmapiff]
      rintro ⟨_, hall⟩
      exact hi 0 (by rw [hall i, tN_zero])

end CompanionTheory.Groth

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum =====
