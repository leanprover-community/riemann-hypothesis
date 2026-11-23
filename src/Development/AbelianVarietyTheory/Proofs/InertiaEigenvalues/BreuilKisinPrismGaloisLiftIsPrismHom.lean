module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PrismTwist

variable {l : ℕ} [hl : Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : GlobalTheory.BKReal.PiSys l e)

theorem ev_injective : Function.Injective (ϖ.ev a) := by
  apply GlobalTheory.BKCoord.ev_injective <;> assumption

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff, WittVector.map_coeff, GlobalTheory.RingIface.sigA_coeff,
    frobenius_def, frobenius_def, map_pow]

end GlobalTheory.BKGal.PrismTwist

theorem GlobalTheory.BKGal.PrismTwist.hom_restrict : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (g : GQ l) (σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a))), (∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l)) → ∀ (ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧), (∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x)) → ∃ H : Hom (ϖ.prism a) ((ϖ.prism a).restrict σ), ∀ x, H.f x = ψ x := by
  intro l _ a e _ _ ϖ g σ hσ ψ hψ
  have hfrob : ∀ x, ψ (frobS l a x) = frobS l a (ψ x) := fun x =>
    GlobalTheory.BKGal.PrismTwist.ev_injective a ϖ (by
      rw [hψ, PiSys.ev_frobS, PiSys.ev_frobS, hψ, GlobalTheory.BKGal.PrismTwist.σA_frobenius])
  refine ⟨{ f := ψ
            f_δ := (deltaS l a).map_δ_of_map_φ (deltaS l a)
              (fun x hx => (mul_eq_zero.1 hx).resolve_left (l_ne_zero l a)) ψ hfrob
            f_I := fun (x : (Wq l a)⟦X⟧) hx => ?_
            f_str := fun r (x : (Wq l a)⟦X⟧) h => ?_ }, fun _ => rfl⟩
  · have hx' := Ideal.mem_span_singleton.1 hx
    refine Ideal.mem_span_singleton.2 ((ϖ.theta_ev_eq_zero_iff a (ψ x)).1 ?_)
    rw [hψ, GlobalTheory.RingBasics.θ_σA, (ϖ.theta_ev_eq_zero_iff a x).2 hx', map_zero]
  · apply ϖ.quotToOC_injective a
    change ϖ.quotToOC a (Ideal.Quotient.mk _ (ψ x)) = ϖ.quotToOC a (ϖ.strMap a (σ r))
    have h' : Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r := h
    rw [PiSys.quotToOC_mk, PiSys.quotToOC_strMap, hψ, GlobalTheory.RingBasics.θ_σA, ← PiSys.quotToOC_mk, h',
      PiSys.quotToOC_strMap]
    refine Subtype.ext ?_
    rw [GlobalTheory.RingIface.sigO_coe]
    change Per.σC g (((r : ↥(ϖ.field a).1) : Om l) : ℂ_[l]) = (((σ r : ↥(ϖ.field a).1) : Om l) : ℂ_[l])
    rw [hσ]
    exact GlobalTheory.RingBasics.σC_coe g _
