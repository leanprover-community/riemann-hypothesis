module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEquivOfFinrank
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

@[expose] public section

open NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.PELU GlobalTheory.UPel.HT
open scoped Matrix TensorProduct Classical

private theorem exists_equiv_of_finrank {F : Type} [Field F] [NumberField F] {V V' : Type}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V']
    (φ : 𝓞 F →+* Module.End ℚ V) (φ' : 𝓞 F →+* Module.End ℚ V')
    (h : Module.finrank ℚ V = Module.finrank ℚ V') :
    ∃ e : V ≃ₗ[ℚ] V', ∀ (c : 𝓞 F) (v : V), e (φ c v) = φ' c (e v) :=
  _root_.UpperTheory.Reformulated.B.ExistsEquivOfFinrank.exists_equiv_of_finrank φ φ' h

private def repOn {O M : Type} [Ring O] [AddCommGroup M] [Module O M] :
    O →+* Module.End ℚ (ℚ ⊗[ℤ] M) :=
  ((Module.End.baseChangeHom ℤ ℚ M).toRingHom).comp (Module.toModuleEnd ℤ M)

private theorem repOn_apply {O M : Type} [Ring O] [AddCommGroup M] [Module O M] (b : O) :
    (repOn b : Module.End ℚ (ℚ ⊗[ℤ] M)) = (DistribSMul.toLinearMap ℤ M b).baseChange ℚ := rfl

theorem UpperTheory.exists_rational_equiv_of_rank :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (Y : PLat D.O D.inv), Function.Surjective (algebraMap (𝓞 D.F) D.O) → Module.finrank ℤ Y.La = Module.finrank ℤ D.La → ∃ e : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D, ∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), e ((DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (e u) := by
  intro p _ D Y hs hr
  haveI := D.freeLa
  haveI := D.finLa
  have hfin : Module.finrank ℚ (ℚ ⊗[ℤ] Y.La) = Module.finrank ℚ (VQ D) := by
    rw [Module.finrank_baseChange, Module.finrank_baseChange, hr]
  obtain ⟨e, he⟩ := exists_equiv_of_finrank (F := D.F)
    ((repOn (O := D.O) (M := Y.La)).comp (algebraMap (𝓞 D.F) D.O))
    ((repOn (O := D.O) (M := D.La)).comp (algebraMap (𝓞 D.F) D.O)) hfin
  refine ⟨e, fun c u => ?_⟩
  obtain ⟨c, rfl⟩ := hs c
  exact he c u
