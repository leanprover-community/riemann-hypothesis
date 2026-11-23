module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RaTpowSinglePow
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivationCommutesWithTraceStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidFinPf
public import Mathlib.Algebra.DualNumber
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {n : ℕ}

theorem frac_deriv (D : Derivation K R R) :
    ∃ D' : Derivation K (FractionRing R) (FractionRing R),
      ∀ r, D' (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing R) (D r) := by
  let φ : R →+* TrivSqZeroExt (FractionRing R) (FractionRing R) :=
    { toFun := fun r => TrivSqZeroExt.inl (algebraMap R (FractionRing R) r) +
        TrivSqZeroExt.inr (algebraMap R (FractionRing R) (D r))
      map_one' := by ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp [D.leibniz, mul_comm, -DualNumber.inr_eq_smul_eps]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp [-DualNumber.inr_eq_smul_eps] }
  have hu : ∀ s : nonZeroDivisors R, IsUnit (φ s) := fun s =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
      simpa [φ] using IsLocalization.map_units (FractionRing R) s)
  let Λ : FractionRing R →+* TrivSqZeroExt (FractionRing R) (FractionRing R) := IsLocalization.lift hu
  have hΛ : ∀ r, Λ (algebraMap R (FractionRing R) r) = φ r := fun r => IsLocalization.lift_eq hu r
  have hfst : ∀ x, (Λ x).fst = x := fun x => by
    have : (TrivSqZeroExt.fstHom (FractionRing R) (FractionRing R) (FractionRing R)).toRingHom.comp Λ =
        RingHom.id _ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
      simp [hΛ, φ]
    exact congr($this x)
  have hsnd : ∀ r, (Λ (algebraMap R (FractionRing R) r)).snd = algebraMap R (FractionRing R) (D r) := fun r => by
    rw [hΛ]
    simp [φ, -DualNumber.inr_eq_smul_eps]
  have hmul : ∀ x y, (Λ (x * y)).snd = x • (Λ y).snd + y • (Λ x).snd := fun x y => by
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  have hK : ∀ c : K, (Λ (algebraMap K (FractionRing R) c)).snd = 0 := fun c => by
    rw [IsScalarTower.algebraMap_apply K R (FractionRing R), hsnd, D.map_algebraMap, map_zero]
  let e : FractionRing R →ₗ[K] FractionRing R :=
    { toFun := fun x => (Λ x).snd
      map_add' := fun x y => by rw [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, Algebra.smul_def, hmul, hK, smul_zero, add_zero, algebraMap_smul] }
  exact ⟨Derivation.mk' e fun x y => hmul x y, fun r => hsnd r⟩

theorem fldF_findim (t : Fin (n + 1) → Rˣ) (Bu : Subalgebra K R) (hTB : torusS K t Finset.univ ≤ Bu) (hFG : Bu.FG)
    (hInt : ∀ b ∈ Bu, IsIntegral (torusS K t Finset.univ) b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b) :
    FiniteDimensional (fldF K t) (FractionRing R) :=
  fldF_findim_pf t Bu hTB hFG hInt hFrac

theorem torus_mem_fldF (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) :
    ∀ r ∈ torusS K t S, algebraMap R (FractionRing R) r ∈ fldF K t := fun r hr =>
  fldF_findim_pf_mem t r (torusS_le_univ t S hr)

theorem trace_deriv [CharZero K] (t : Fin (n + 1) → Rˣ) [FiniteDimensional (fldF K t) (FractionRing R)] (D : Derivation K R R)
    (hD : ∀ j, D (t j : R) ∈ Set.range (algebraMap K R)) (y b : R) (hb : b ∈ torusS K t Finset.univ)
    (hy : algebraMap (fldF K t) (FractionRing R)
      (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) y)) = algebraMap R (FractionRing R) b) :
    algebraMap (fldF K t) (FractionRing R)
      (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) (D y))) =
        algebraMap R (FractionRing R) (D b) := by
  obtain ⟨Dl, hDl⟩ := frac_deriv D

  have hF : ∀ x ∈ fldF K t, Dl x ∈ fldF K t := fun x hx => by
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hD j
      rw [hDl, ← hc, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ c
    | algebraMap c =>
      rw [Derivation.map_algebraMap]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | inv x hx0 hx =>
      rw [Derivation.leibniz_inv, smul_eq_mul]
      exact mul_mem (neg_mem (pow_mem (inv_mem hx0) 2)) hx
    | mul x y hx0 hy0 hx hy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (mul_mem hx0 hy) (mul_mem hy0 hx)
  let e : fldF K t →ₗ[K] fldF K t :=
    { toFun := fun x => ⟨Dl (x : FractionRing R), hF _ x.2⟩
      map_add' := fun x y => Subtype.ext (map_add Dl (x : FractionRing R) y)
      map_smul' := fun c x => Subtype.ext (Dl.map_smul c (x : FractionRing R)) }
  let D0 : Derivation K (fldF K t) (fldF K t) :=
    Derivation.mk' e fun x y => Subtype.ext (by
      change Dl ((x : FractionRing R) * y) = (x : FractionRing R) * Dl (y : FractionRing R) +
        (y : FractionRing R) * Dl (x : FractionRing R)
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
  have hD0 : ∀ x : fldF K t, Dl (algebraMap (fldF K t) (FractionRing R) x) =
      algebraMap (fldF K t) (FractionRing R) (D0 x) := fun _ => rfl
  have key := GlobalTheory.T.derivation_commutes_with_trace K (fldF K t) (FractionRing R) Dl D0 hD0 (algebraMap R (FractionRing R) y)
  rw [← hDl, ← key, ← hD0, hy, hDl]

end CrystallineSemistableComparison.Pb
