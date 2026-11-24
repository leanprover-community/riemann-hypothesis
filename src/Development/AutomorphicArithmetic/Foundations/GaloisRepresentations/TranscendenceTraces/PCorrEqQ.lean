module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtDegConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem hl_rel (hTr : TrHl) (hC : CorrEq) (l : ℕ) [Fact l.Prime] (n i : ℤ) {S Y B : Scheme.{0}} (bS : S ⟶ B) (bY : Y ⟶ B)
    [IsSeparated bY] [LocallyOfFiniteType bY] (ι : Type) [Fintype ι] (c : ι → Corr S Y) (m : ι → ℤ)
    (hb : ∀ a, (c a).f ≫ bY = (c a).p ≫ bS) (hl : IsUnit (l : Γ(S, ⊤))) (D : Set S) (hD : Dense D)
    (hz : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y), pt x ∈ D →
      ∑ a, m a * (c a).cyc Ω x y = 0) :
    ∑ a, m a • (trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) = 0 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hl.pow k
  have h := hC (l ^ k) n i bS bY ι c m hb hq D hD hz (x.1 k)
  have e : ∀ a, ((trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) x).1 k =
      (c a).op (l ^ k) n i (x.1 k) := fun a => by
    haveI := (c a).fin
    exact hTr l n i (c a).p (c a).w (c a).wt hl _ k
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h
  change m a • ((trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) x).1 k = _
  rw [e a]
  rfl

theorem UpperTheory.Gal.TranscendenceTraces.corrEqQ_of :
    TrHl → CorrEq → CorrEqQ := by
  intro hTr hC l _ n i S Y B bS bY _ _ ι _ c m hb hl D hD hz
  have h := hl_rel hTr hC l n i bS bY ι c m hb hl D hD hz
  have e : ∀ a, Corr.opQ l (c a) n i = LinearMap.baseChangeHom ℤ_[l] ℚ_[l] _ _
      (trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) := by
    intro a
    rw [LinearMap.baseChangeHom_apply, LinearMap.baseChange_comp]
    rfl
  simp only [e, Int.cast_smul_eq_zsmul]
  simp_rw [← map_zsmul]

  rw [← map_sum, h, map_zero]
