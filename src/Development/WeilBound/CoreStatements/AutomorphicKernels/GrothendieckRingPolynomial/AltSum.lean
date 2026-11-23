module

import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltComb
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjectiveStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos



namespace PositivityTheory.Groth.AltS

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tN (Δ : Segment k) (n : ℕ) : IrrGL (k := k) := Δ.first.nu (n : ℂ)

theorem tN_injective (Δ : Segment k) : Function.Injective (tN Δ) := fun a b h =>
  GlobalTheory.T.cuspidal_twist_injective PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ.first Δ.isCusp_first a b h

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

end PositivityTheory.Groth.AltS

namespace PositivityTheory.Groth

open AltS

theorem altSum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    AltSum k := by
  apply CompanionTheory.Groth.altSum <;> assumption

end PositivityTheory.Groth

end
