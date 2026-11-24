module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

namespace GlobalTheory.BumpData

theorem exists_enum {X : Type} (M : Multiset X) {a : ℕ} (h : M.card = a) :
    ∃ f : Fin a → X, Finset.univ.val.map f = M := by
  subst h
  obtain ⟨l, rfl⟩ := Quotient.exists_rep M
  refine ⟨fun i => l.get ⟨i, by simpa using i.2⟩, ?_⟩
  rw [Fin.univ_val_map]
  congr 1
  apply List.ext_get (by simp)
  intro n h1 h2
  simp

theorem bumpData : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (π₀ : CuspSub E a) (ω : HChar E),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧ π₀.IsUnitary ∧
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, HasSatGL w.1 (π₀.locRep w.1) (Finset.univ.val.map (α w)) := by
  intro E _ _ _ a π hπ T hT
  induction π using Quotient.inductionOn with | _ π₀ => ?_
  obtain ⟨ω, hωu, hω⟩ := hπ
  have hsat : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, (CG.mk π₀).HasSat w.1 (sat (CG.mk π₀) w.1) := by
    intro w
    have hx : ∃ B, (CG.mk π₀).HasSat w.1 B := hT w.1 w.2
    unfold sat
    rw [dite_eq_left hx]
    exact hx.choose_spec
  have hα : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, ∃ f : Fin a → ℂˣ,
      Finset.univ.val.map f = sat (CG.mk π₀) w.1 := fun w => exists_enum _ (hsat w).card
  choose α hα using hα
  refine ⟨α, π₀, ω, hα, rfl, hωu, hω, ⟨ω, hωu, CuspSub.hasCentral_iff.2 hω⟩, fun w => ?_⟩
  rw [hα w]
  exact hsat w

end GlobalTheory.BumpData
