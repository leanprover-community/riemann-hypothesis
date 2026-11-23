module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.JHMult
open PositivityTheory.Rg.BcN.F2 (FinSubq)

namespace GlobalTheory.CompanionTheory.RepFinSubq

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_series {ρ : Representation F G V} (h : HasFiniteLength ρ) :
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧
      ∀ t : Fin N, S t.castSucc ⋖ S t.succ := by
  obtain ⟨s, h0, h1⟩ := isFiniteLength_iff_exists_compositionSeries.1 h
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm
  refine ⟨s.length, fun i => e (s i), ?_, ?_, ?_, fun t => ?_⟩
  · exact e.monotone.comp s.strictMono.monotone
  · show e s.head = ⊥
    rw [h0, map_bot]
  · show e s.last = ⊤
    rw [h1, map_top]
  · exact (apply_covBy_apply_iff e).2 (s.step t)

theorem isSubquotient_subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    IsSubquotient (subQuot S T) ρ :=
  ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

theorem exists_factor_equiv {ρ : Representation F G V} {N : ℕ} {S : Fin (N + 1) → Subrepresentation ρ}
    (hS : Monotone S) (h0 : S 0 = ⊥) (h1 : S (Fin.last N) = ⊤) (hc : ∀ t : Fin N, S t.castSucc ⋖ S t.succ)
    {τ : Representation F G W} (hτ : τ.IsIrreducible) (hq : IsSubquotient τ ρ) :
    ∃ t : Fin N, Nonempty (τ.Equiv (subQuot (S t.succ) (S t.castSucc))) := by
  have hne : jhMult τ ρ ≠ 0 := jhMult_ne_zero_iff.2 hq
  rw [jhMult_filtration hτ S hS h0 h1] at hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨e⟩ := (jhMult_ne_zero_iff.1 ht).nonempty_equiv hτ (isIrreducible_subQuot (hc t))
  exact ⟨t, ⟨e.symm⟩⟩

theorem finSubq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  intro F _ _ _ _ ι _ _ U _ _ ρ hρ hfl
  obtain ⟨N, S, hS, h0, h1, hc⟩ := exists_series hfl
  refine ⟨Fin N, inferInstance, fun t => _, fun _ => inferInstance, fun _ => inferInstance,
    fun t => subQuot (S t.succ) (S t.castSucc), fun t => ?_, fun W' _ _ τ' hτ hq => ?_⟩
  · exact ⟨(isSubquotient_subQuot _ _).isSmooth hρ, isIrreducible_subQuot (hc t), isSubquotient_subQuot _ _⟩
  · exact exists_factor_equiv hS h0 h1 hc hτ hq

end GlobalTheory.CompanionTheory.RepFinSubq
