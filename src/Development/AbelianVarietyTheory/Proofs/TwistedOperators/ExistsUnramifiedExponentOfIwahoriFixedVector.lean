module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

@[expose] public section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL

theorem exists_expMult_ne_zero_of_fixed_iwahori (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsAdmissible π)
    (h : fixed π (iwahori k (Fin n)) ≠ ⊥) : ∃ χ : (Fin n → kˣ) →* ℂˣ, expMult π χ ≠ 0 := by
  haveI := hπ.2 _ (IwahoriOnto.isOpen_iwahori k (Fin n)) (IwahoriOnto.isCompact_iwahori k (Fin n))
  have hb := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hπ
  haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) :=
    Module.Finite.of_surjective _ hb.2
  haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 h
  haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial
  obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ (Fin n → kˣ) _
    (jacBUFixed π) fun a b => by rw [← map_mul, mul_comm, map_mul]
  let ι : (ofChar ψ).IntertwiningMap (jacBUFixed π) :=
    ⟨LinearMap.toSpanSingleton ℂ _ v, fun g => by
      refine LinearMap.ext_ring ?_
      simp [hψ]⟩
  exact ⟨ψ, JHMult.jhMult_ne_zero_iff.2 (IsSubquotient.of_injective ι (smul_left_injective ℂ hv))⟩

end GlobalTheory.SmGL
