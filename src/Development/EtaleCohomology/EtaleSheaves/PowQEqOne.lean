module

import Development.EtaleCohomology.KummerTheory.PrimTorsPf
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfA

theorem pow_q_eq_one {q : ℕ} {B : Type} [CommRing B] (x : B)
    (hx : Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0) : x ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (Polynomial.aeval x) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hx, zero_mul] at this
  exact sub_eq_zero.1 this

theorem local_eq {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {x y : B}
    (hx : x ^ q = 1) (hy : y ^ q = 1) (hr : IsLocalRing.residue B x = IsLocalRing.residue B y) : x = y := by
  apply (config := { allowSynthFailures := true }) LateralTheory.KummerTheory.PrimitiveRootTorsion.uniq <;> assumption

theorem res_root {q : ℕ} {B : Type} [CommRing B] [IsLocalRing B] (z : B)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) :
    Polynomial.IsRoot (Polynomial.cyclotomic q (IsLocalRing.ResidueField B)) (IsLocalRing.residue B z) := by
  have h := Polynomial.aeval_algHom_apply (IsLocalRing.residue B).toIntAlgHom z (Polynomial.cyclotomic q ℤ)
  rw [hz, map_zero] at h
  rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def, Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem local_pow {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {ζ ξ : B}
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = ζ ^ (a : ZMod q).val := by
  have : NeZero ((q : ℕ) : IsLocalRing.ResidueField B) :=
    ⟨by simpa [map_natCast] using (hq.map (IsLocalRing.residue B)).ne_zero⟩
  have root : ∀ z : B, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
      IsPrimitiveRoot (IsLocalRing.residue B z) q := fun z hz =>
    Polynomial.isRoot_cyclotomic_iff.1 (res_root z hz)
  obtain ⟨i, hi, hpow⟩ := (root ζ hζ).eq_pow_of_pow_eq_one ((root ξ hξ).pow_eq_one)
  have hc : i.Coprime q :=
    ((root ζ hζ).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hpow ▸ root ξ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine local_eq hq (pow_q_eq_one ξ hξ) ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, pow_q_eq_one ζ hζ, one_pow]
  · rw [map_pow]; exact hpow.symm

end LateralTheory.E.LeafTw0LocGenPfA
