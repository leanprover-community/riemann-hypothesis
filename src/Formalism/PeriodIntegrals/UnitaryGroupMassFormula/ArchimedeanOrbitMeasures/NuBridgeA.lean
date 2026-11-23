module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MuBridgeA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTestC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.StdConjExOfWitt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv

@[expose] public section

noncomputable section

namespace PI.AprimeInfW.NuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

section Tr

variable {D : D7} (X : HidaSetting D)

theorem emb_real (v : InfinitePlace X.B.I.F) (a : X.B.I.F) : conj (v.embedding a) = v.embedding a := by
  have hv : v.IsReal := totReal_of X v
  have h := NumberField.ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hv)
  have := RingHom.congr_fun h a
  simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this

theorem phi_star (v : InfinitePlace X.B.I.F) (e : X.B.I.E) : X.B.I.φ v (star e) = conj (X.B.I.φ v e) :=
  X.B.I.cm.cmUnram.2.1 _ e

theorem phi_notReal (v : InfinitePlace X.B.I.F) : ¬ ∀ e : X.B.I.E, conj (X.B.I.φ v e) = X.B.I.φ v e := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal (X.B.I.φ v) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext e
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq, h e]
  have hc := X.B.I.cm.cmUnram.1.isComplex (InfinitePlace.mk (X.B.I.φ v))
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem emb_trace (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    v.embedding (Algebra.trace X.B.I.F X.B.I.E e) = X.B.I.φ v e + conj (X.B.I.φ v e) := by
  apply PI.AprimeInfW.MuB.emb_trace <;> assumption

theorem evInf_conj (v : InfinitePlace X.B.I.F) (a : Ainf X.B.I.F) :
    conj (PI.AprimeInfU.evInf X v a) = PI.AprimeInfU.evInf X v a := by
  have hv : v.IsReal := totReal_of X v
  show conj (InfinitePlace.Completion.extensionEmbedding v (a v)) =
    InfinitePlace.Completion.extensionEmbedding v (a v)
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem evInf_alg (v : InfinitePlace X.B.I.F) (a : X.B.I.F) :
    PI.AprimeInfU.evInf X v (algebraMap X.B.I.F (Ainf X.B.I.F) a) = v.embedding a :=
  evV_algebraMap X.B.I v a

theorem trace_one_tmul (e : X.B.I.E) :
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) =
      algebraMap X.B.I.F (Ainf X.B.I.F) (Algebra.trace X.B.I.F X.B.I.E e) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem evInf_trace (v : InfinitePlace X.B.I.F) (z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.evInf X v (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) z) =
      PI.AprimeInfU.thetaInf X v z + conj (PI.AprimeInfU.thetaInf X v z) := by
  apply PI.AprimeInfW.MuB.evInf_trace <;> assumption

theorem theta_sigR (v : InfinitePlace X.B.I.F) (t : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (sigR (Ainf X.B.I.F) X.B.I.cm.sig t) = conj (PI.AprimeInfU.thetaInf X v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : sigR (Ainf X.B.I.F) X.B.I.cm.sig (a ⊗ₜ[X.B.I.F] e) = a ⊗ₜ[X.B.I.F] (star e) := rfl
    rw [h, thetaInf_tmul, thetaInf_tmul, map_mul, evInf_conj, phi_star]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem theta_alg (v : InfinitePlace X.B.I.F) (q : X.B.I.F) :
    PI.AprimeInfU.thetaInf X v (algebraMap X.B.I.F (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) q) = v.embedding q := by
  rw [Algebra.TensorProduct.algebraMap_apply, thetaInf_tmul, evInf_alg, map_one, mul_one]

theorem theta_surj (z : InfinitePlace X.B.I.F → ℂ) :
    ∃ y : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E, ∀ v, PI.AprimeInfU.thetaInf X v y = z v := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let b : Module.Basis (Fin 2) X.B.I.F X.B.I.E := Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2
  have hr : ∀ v : InfinitePlace X.B.I.F, ∃ r : Fin 2 → ℝ,
      (r 0 : ℂ) * X.B.I.φ v (b 0) + (r 1 : ℂ) * X.B.I.φ v (b 1) = z v := by
    intro v
    let f : Fin 2 → ℂ := ![X.B.I.φ v (b 0), X.B.I.φ v (b 1)]
    have hli : LinearIndependent ℝ f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_two] at hg
      have key := theta_lin_indep (X.B.I.φ v) (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E)
        (fun a => X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) a)
        (fun a ha => RingHom.mem_range.1 ((X.B.I.cm.fixed a).1 ha)) b g (by
          simpa [f, Complex.real_smul] using hg)
      intro i
      fin_cases i
      · exact key.1
      · exact key.2
    have hsp : Submodule.span ℝ (Set.range f) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simp [Complex.finrank_real_complex])
    have hz : z v ∈ Submodule.span ℝ (Set.range f) := by rw [hsp]; trivial
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
    refine ⟨r, ?_⟩
    rw [← hr, Fin.sum_univ_two]
    simp [f, Complex.real_smul]
  choose r hr using hr
  have hv : ∀ v : InfinitePlace X.B.I.F, v.IsReal := fun v => totReal_of X v
  let c : Fin 2 → Ainf X.B.I.F := fun i =>
    (fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hv w)).symm (r w i) :
      ∀ w : InfinitePlace X.B.I.F, w.Completion)
  have hc : ∀ i v, PI.AprimeInfU.evInf X v (c i) = (r v i : ℂ) := by
    intro i v
    show InfinitePlace.Completion.extensionEmbedding v
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (hv v)).symm (r v i)) = _
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hv v),
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply (hv v), RingEquiv.apply_symm_apply]
  refine ⟨c 0 ⊗ₜ[X.B.I.F] b 0 + c 1 ⊗ₜ[X.B.I.F] b 1, fun v => ?_⟩
  rw [map_add (f := _), thetaInf_tmul, thetaInf_tmul, hc, hc, hr]

end Tr

end PI.AprimeInfW.NuB
