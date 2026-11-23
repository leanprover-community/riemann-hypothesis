module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentTermInjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
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

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkSegSocle

theorem dec_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Function.Injective (dec Δ) :=
  (GlobalTheory.T.segment_term_injective hA Δ).comp Fin.rev_injective

theorem ncard_perm_dec_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) :
    Set.ncard {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ≤ 1 := by
  have hinj := dec_injective hA Δ
  have hsub : {e : Fin Δ.len ≃ Fin Δ.len | ∀ a, dec Δ a = dec Δ (e a)} ⊆ {Equiv.refl _} := by
    intro e he
    simp only [Set.mem_setOf_eq] at he
    rw [Set.mem_singleton_iff]
    exact Equiv.ext fun a => (hinj (he a)).symm
  calc _ ≤ ({Equiv.refl _} : Set (Fin Δ.len ≃ Fin Δ.len)).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_singleton _)
    _ = 1 := Set.ncard_singleton _

theorem exists_isSocle_prodIrr_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N), ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr (dec Δ) hd) := by
  intro k _ _ _ _ hA Δ N hd
  apply GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_jm_le_one hA (dec Δ) hd
  have hc : ∀ a, (dec Δ a).IsCusp := fun a => Δ.isCusp_term (Fin.rev a)
  rw [GlobalTheory.T.jacquet_multiplicity_cuspidal_product hA (dec Δ) (dec Δ) hd hd hc hc]
  exact_mod_cast ncard_perm_dec_le_one hA Δ

end GlobalTheory.CompanionTheory.LkSegSocle

end
