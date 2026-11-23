module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleModuleIffLatticeQuotients
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk

@[expose] public section



open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem finite_Xq {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)) (hlam : Irreducible lam) (a : ℕ) :
    Finite ↥(Xq ↥LL.1 lam a) := by
  classical
  haveI := GlobalTheory.FullCharpoly.hasFiniteQuotients_OL LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hne : lam ^ a ≠ 0 := pow_ne_zero _ hlam.ne_zero
  have hK : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) ≠ 0 := by
    intro h; exact hne (hinj (by rw [h, map_zero]))
  haveI : Finite (↥(OL LL) ⧸ Ideal.span {lam ^ a}) := Ring.HasFiniteQuotients.finiteQuotient (by
    rwa [Ne, Ideal.span_singleton_eq_bot])
  have hex : ∀ x : ↥(Xq ↥LL.1 lam a), ∃ c : ↥(OL LL), ∃ s : ↥LL.1,
      Submodule.Quotient.mk (p := intO (O := ↥(OL LL)) ↥LL.1) s = x.1 ∧ algebraMap ↥(OL LL) ↥LL.1 c = lam ^ a • s := by
    intro x
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx := x.2
    simp only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx
    rw [← hs, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, s, hs, hc⟩
  let f : ↥(Xq ↥LL.1 lam a) → ↥(OL LL) ⧸ Ideal.span {lam ^ a} := fun x => Ideal.Quotient.mk _ (hex x).choose
  refine Finite.of_injective f ?_
  intro x y hxy
  obtain ⟨s, hs, hc⟩ := (hex x).choose_spec
  obtain ⟨t, ht, hd⟩ := (hex y).choose_spec
  have h1 := hxy
  simp only [f, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨d, hd'⟩ := h1
  apply Subtype.ext
  rw [← hs, ← ht, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  refine ⟨d, ?_⟩
  have h2 : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * (s - t) = algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * algebraMap ↥(OL LL) ↥LL.1 d := by
    rw [← map_mul, mul_comm (lam ^ a) d, hd', map_sub, hc, hd, Algebra.smul_def, Algebra.smul_def, mul_sub]
  have := mul_left_cancel₀ hK h2
  simp only [Algebra.linearMap_apply]
  exact this.symm

end GlobalTheory.UseLoc.Cases
