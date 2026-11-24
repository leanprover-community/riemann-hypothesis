module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
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
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem bkStr_quotient_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  intro l _ a _ O _ _ π Ep hE hπ
  obtain ⟨hmon, -, hdvd, -⟩ := hE
  obtain ⟨h0, hsurj, hker⟩ := hπ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have H : Ep.IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun hn => Ideal.mem_span_singleton.2 (hdvd _ hn)
      monic := hmon }
  have hK : RingHom.ker (Polynomial.aeval (R := Wq l a) π) = Ideal.span {Ep} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · exact hker f
    · rintro ⟨g, rfl⟩
      simp [h0]
  let e1 := Ideal.quotientKerAlgEquivOfSurjective (f := Polynomial.aeval (R := Wq l a) π)
    (fun x => hsurj x)
  let e2 := Ideal.quotientEquivAlgOfEq (Wq l a) hK
  let e := (e1.symm.trans (e2.trans H.algEquivQuotient)).toRingEquiv
  refine ⟨e, fun f => ?_⟩
  have h1 : e1.symm (Polynomial.aeval π f) = Ideal.Quotient.mk _ f := by
    apply e1.injective
    simp only [AlgEquiv.apply_symm_apply, e1]
    rfl
  simp only [e, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, h1]
  simp [e2, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]

end GlobalTheory
