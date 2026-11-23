module

public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.ExpFrame

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

theorem exists_unif_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (l : ℕ)
    (hl : l ≠ 0) (hu : ¬ IsUnit ((l : ℕ) : O)) :
    ∃ (ϖ : O) (n : ℕ), Irreducible ϖ ∧ ϖ ∣ (l : O) ∧ (l : O) ∣ ϖ ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : ((l : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  refine ⟨ϖ, n, hϖ, ?_, hn.dvd⟩
  rcases n with _ | n
  · exact absurd (hn.isUnit_iff.2 (by simp)) hu
  · exact (dvd_pow_self ϖ n.succ_ne_zero).trans hn.symm.dvd

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

section Sub

variable {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} (X : HidaSetting ι N lam) (ϖ : X.O)

abbrev Red : Type := NablaT X.O N lam ⧸ scaleSub X.A (NablaT X.O N lam) ϖ

abbrev SimpIx : Type :=
  Σ E : Submodule X.A (Red X ϖ), {N' : Submodule X.A E // IsSimpleModule X.A (E ⧸ N')}

abbrev SimpMod (μ : SimpIx X ϖ) : Type := μ.1 ⧸ μ.2.1

variable {X ϖ}

theorem exists_simpMod (Gm : Type) [AddCommGroup Gm] [Module X.A Gm] [IsSimpleModule X.A Gm]
    (h : IsSubquot X.A (Red X ϖ) Gm) :
    ∃ μ : SimpIx X ϖ, Nonempty (Gm ≃ₗ[X.A] SimpMod X ϖ μ) := by
  obtain ⟨E, ψ, hψ⟩ := h
  let e := ψ.quotKerEquivOfSurjective hψ
  haveI : IsSimpleModule X.A (E ⧸ LinearMap.ker ψ) := IsSimpleModule.congr e
  exact ⟨⟨E, LinearMap.ker ψ, inferInstance⟩, ⟨e.symm⟩⟩

end Sub

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

section SubF

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) [mT : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))]
  [@IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) _ mT.toSMul _]
  (m : Ideal F.T) [m.IsPrime] (ϖ : F.O)

end SubF

end GlobalTheory.ExpModel

end
