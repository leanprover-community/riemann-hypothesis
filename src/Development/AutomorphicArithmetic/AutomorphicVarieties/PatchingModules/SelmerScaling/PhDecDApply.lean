module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TpDual
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private noncomputable def UpperTheory.V.Pa.phDecD {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) : S.Bh →+ S.F where
  toFun b := Φ (b • y) - S.rF b * Φ y
  map_zero' := by simp
  map_add' b b' := by rw [add_smul, map_add (f := _), map_add (f := _)]; ring

private theorem UpperTheory.V.Pa.phDecD_apply {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) (b : S.Bh) :
    phDecD S Φ y b = Φ (b • y) - S.rF b * Φ y := rfl

private theorem UpperTheory.V.Pa.phDecD_mem {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (hΦ : Φ ∈ S.Ph)
    (y : S.U.N) : phDecD S Φ y ∈ S.Tp := by
  obtain ⟨h1, h2⟩ := hΦ
  have hm : ∀ q ∈ maximalIdeal S.Bh, S.rF q = 0 := fun q hq => by
    rw [← S.rF_ker] at hq; exact hq
  have dec : ∀ b : S.Bh, ∃ (o : S.OO) (q : S.Bh), q ∈ maximalIdeal S.Bh ∧ b = algebraMap S.OO S.Bh o + q := by
    intro b
    obtain ⟨o, ho⟩ := S.oo_surj (S.rF b)
    refine ⟨o, b - algebraMap S.OO S.Bh o, ?_, by ring⟩
    rw [← S.rF_ker, RingHom.mem_ker, map_sub, ← ho]
    simp
  refine ⟨fun b b' => ?_, fun o => ?_, fun b hb => ?_⟩
  · obtain ⟨o, q, hq, rfl⟩ := dec b
    obtain ⟨o', q', hq', rfl⟩ := dec b'
    have hqq : q * q' ∈ S.J2 := by
      refine Ideal.mem_sup_left (Ideal.mem_sup_right ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul hq hq'
    have e : ((algebraMap S.OO S.Bh o + q) * (algebraMap S.OO S.Bh o' + q')) • y =
        algebraMap S.OO S.Bh o • (algebraMap S.OO S.Bh o' • y) + algebraMap S.OO S.Bh o • (q' • y) +
          algebraMap S.OO S.Bh o' • (q • y) + (q * q') • y := by
      simp only [smul_smul, ← add_smul]
      congr 1
      ring
    simp only [phDecD_apply]
    rw [e]
    simp only [add_smul, map_add (f := _), map_mul, h1, h2 _ hqq, hm q hq, hm q' hq']
    ring
  · rw [phDecD_apply, h1, sub_self]
  · have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
      refine Ideal.span_le.2 ?_
      rintro a ⟨x, hx, z, hz, e⟩
      obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx z hz
      have : a = c := S.U.inj (e.symm.trans e')
      rw [this]
      exact hc
    rw [phDecD_apply, h2 b (Ideal.mem_sup_right hb), hm b (hi hb)]
    simp

private theorem UpperTheory.V.Pa.phDec_expand {F A : Type} [Field F] [AddCommGroup A] (T : Submodule F (A →+ F)) {e : ℕ}
    (v : Module.Basis (Fin e) F T) (d : T) (b : A) :
    (d : A →+ F) b = ∑ k, (v k : A →+ F) b * v.coord k d := by
  let ev : T →ₗ[F] F :=
    { toFun := fun α => (α : A →+ F) b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev d = ∑ k, ev (v k) * v.coord k d

  conv_lhs => rw [← v.sum_repr d, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, Module.Basis.coord_apply]

theorem UpperTheory.V.Pa.phDec :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Φ ∈ S.Ph, ∃ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) ∧ (∀ k, μ k ∈ S.La) ∧ ∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y := by
  intro l _ S Φ hΦ
  have : Module.Finite S.F S.Tp := (tpDual l S).1
  let v := Module.finBasis S.F S.Tp
  let D : S.U.N →+ S.Tp :=
    { toFun := fun y => ⟨phDecD S Φ y, phDecD_mem S Φ hΦ y⟩
      map_zero' := by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp [phDecD_apply]
      map_add' := fun y y' => by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp only [Submodule.coe_add, AddMonoidHom.add_apply, phDecD_apply, smul_add, map_add (f := _)]
        ring }
  have hD : ∀ y b, (D y : S.Bh →+ S.F) b = Φ (b • y) - S.rF b * Φ y := fun _ _ => rfl
  have hs : ∀ (c : S.Bh) y, D (c • y) = S.rF c • D y := by
    intro c y
    refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
    have := (D y).2.1 b c
    rw [hD, hD, hD, map_mul] at this
    rw [Submodule.coe_smul, AddMonoidHom.smul_apply, hD, hD, smul_smul, smul_eq_mul]
    linear_combination this
  refine ⟨_, fun k => v k, fun k => (v.coord k).toAddMonoidHom.comp D, fun k => (v k).2, fun k c y => ?_,
    fun b y => ?_⟩
  · change v.coord k (D (c • y)) = S.rF c * v.coord k (D y)
    rw [hs, map_smul, smul_eq_mul]
  · have := phDec_expand S.Tp v (D y) b
    rw [hD] at this
    change Φ (b • y) = S.rF b * Φ y + ∑ k, (v k : S.Bh →+ S.F) b * v.coord k (D y)
    rw [← this]
    ring
