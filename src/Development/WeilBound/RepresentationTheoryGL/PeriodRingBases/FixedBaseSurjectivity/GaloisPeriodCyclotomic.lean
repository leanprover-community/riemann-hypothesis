module

public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AwayExistsSelf
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FundIotaTANeZero
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace BaseA

private theorem loc2_lift_apply {A E : Type} [CommRing A] [CommRing E] {a t : A}
    {f : A →+* E} {ha : IsUnit (f a)} {ht : IsUnit (f t)}
    {j : Loc2 a t →+* E} {k : A →+* Loc2 a t}
    (hj : j = Loc2.lift f ha ht) (hk : k = Loc2.mk₀ a t) (x : A) : j (k x) = f x := by
  subst j
  subst k
  exact Loc2.lift_mk₀ f ha ht x

variable (l : ℕ) [Fact l.Prime]

theorem isCrisDR_ι : IsCrisDR l (ι l) := by
  intro x
  -- Use the equations for the bundled maps before applying them to an element.
  exact loc2_lift_apply (ι.eq_def l) (cB.eq_def l) x

theorem ι_eq : ι l = PositivityTheory.LocInh.ιCD l := (PositivityTheory.LocInh.isCrisDR_iff _).1 (isCrisDR_ι l)

theorem qB_eq : qB l = PositivityTheory.LocInh.qB l :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => by
    rw [RingHom.comp_apply, RingHom.comp_apply, qB, IsLocalization.lift_eq]
    exact (PositivityTheory.LocInh.qB_coe z).symm)

theorem ι_cB (y : ACris.ACris ℂ_[l] l) : ι l (cB l y) = iC l y := isCrisDR_ι l y

end BaseA

open BaseA

theorem base_ι_inj (l : ℕ) [Fact l.Prime] : Function.Injective (ι l) := by
  rw [ι_eq]; exact PositivityTheory.LocInh.ιCD_injective

theorem base_dom (l : ℕ) [Fact l.Prime] : IsDomain (B l) :=
  Function.Injective.isDomain (ι l) (base_ι_inj l)

theorem base_σ_one (l : ℕ) [Fact l.Prime] : σB (1 : GQ l) = RingHom.id _ :=
  RingHom.ext fun b => PositivityTheory.LocInh.σB_one b

theorem base_σ_mul (l : ℕ) [Fact l.Prime] : ∀ g h : GQ l, σB (g * h) = (σB g).comp (σB h) :=
  fun g h => RingHom.ext fun b => PositivityTheory.LocInh.σB_mul g h b

theorem base_φ_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) x, φ l (σB g x) = σB g (φ l x) :=
  fun g x => PositivityTheory.LocInh.φB_σB g x

theorem base_ι_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) x, ι l (σB g x) = σD g (ι l x) := by
  intro g x; rw [ι_eq]; exact PositivityTheory.LocInh.ιCD_σB g x

theorem base_φ_q (l : ℕ) [Fact l.Prime] : ∀ q, φ l (qB l q) = qB l q := by
  intro q; rw [qB_eq]; exact PositivityTheory.LocInh.φB_qB q

theorem base_σ_q (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) q, σB g (qB l q) = qB l q := by
  intro g q
  apply base_ι_inj l
  rw [base_ι_σ, ι_eq, qB_eq, PositivityTheory.LocInh.ιCD_qB, PositivityTheory.LocInh.σD_oD, AlgEquiv.commutes]

theorem base_ι_q (l : ℕ) [Fact l.Prime] : ∀ q, ι l (qB l q) = qQ l q := by
  intro q; rw [ι_eq, qB_eq]; exact PositivityTheory.LocInh.fund_ιCD_qB q

theorem period_image_eq (l : ℕ) [Fact l.Prime] : ι l (t l) = tQ l := ι_cB l (tA l)

theorem base_t_unit (l : ℕ) [Fact l.Prime] : IsUnit (t l) := Loc2.isUnit_right _ _

theorem frobenius_period_holds (l : ℕ) [Fact l.Prime] : φ l (t l) = (l : B l) * t l := PositivityTheory.LocInh.φB_tB

theorem galois_period_cyclotomic (l : ℕ) [Fact l.Prime] : ∀ g : GQ l, σB g (t l) = qB l (χ g) * t l := by
  intro g; rw [qB_eq]; exact PositivityTheory.LocInh.σB_tB g

theorem base_χ_cont (l : ℕ) [Fact l.Prime] : Continuous (χ : GQ l → ℚ_[l]) :=
  by
  have h1 : Continuous (fun g : GQ l => ((DeRhamTwist.Twist.chi0 l g : ℤ_[l]ˣ) : ℤ_[l])) :=
    Units.continuous_val.comp (DeRhamTwist.Twist.continuous_cyclotomic_character (l := l))
  have h2 : Continuous (fun x : ℤ_[l] => (x : ℚ_[l])) := continuous_subtype_val
  exact h2.comp h1

private theorem mem_of_mul_pows_mul_eq {K : Type*} [Field K] {S : Subring K}
    {a b z w : K} {m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (haS : a⁻¹ ∈ S) (hbS : b⁻¹ ∈ S) (hw : w ∈ S)
    (h : a ^ m * b ^ n * z = w) : z ∈ S := by
  have hz : z = w * (a⁻¹) ^ m * (b⁻¹) ^ n := by
    rw [inv_pow, inv_pow, mul_assoc, ← mul_inv,
      eq_mul_inv_iff_mul_eq₀ (mul_ne_zero (pow_ne_zero m ha) (pow_ne_zero n hb))]
    exact (mul_comm _ _).trans h
  rw [hz]
  exact S.mul_mem (S.mul_mem hw (S.pow_mem haS m)) (S.pow_mem hbS n)

theorem base_ι_Bst (l : ℕ) [Fact l.Prime] : ∀ x, ι l x ∈ Bst l := by
  intro x
  obtain ⟨m, n, y, h⟩ := PositivityTheory.LocInh.bcris_surj x
  have h1 : (l : BdR l) ^ m * tQ l ^ n * ι l x = iC l y := by
    simpa only [map_mul (ι l), map_pow (ι l), ι_cB, map_natCast (iC l), tQ] using congrArg (ι l) h
  have hl0 : (l : BdR l) ≠ 0 := map_natCast (iC l) l ▸ (isUnit_iC_l l).ne_zero
  have ht0 : tQ l ≠ 0 := DeRhamTwist.Twist.tQ_ne
  have mem : ∀ z ∈ ({((l : BdR l))⁻¹, (tQ l)⁻¹, uQ l} : Set (BdR l)), z ∈ Bst l :=
    fun z hz => Subring.subset_closure (Or.inr hz)
  exact mem_of_mul_pows_mul_eq hl0 ht0
    (mem _ (Set.mem_insert _ _))
    (mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (Subring.subset_closure (Or.inl ⟨y, rfl⟩)) h1

theorem base_u_Bst (l : ℕ) [Fact l.Prime] : uQ l ∈ Bst l :=
  Subring.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem base_fs_ker (l : ℕ) [Fact l.Prime] : ∀ x, φ l x = x → ι l x ∈ Plus l → ∃ q, x = qB l q := by
  intro x hφ hx
  obtain ⟨z, hz⟩ := RingHom.mem_range.1 hx
  rw [ι_eq] at hz
  obtain ⟨q, hq⟩ := PositivityTheory.LocInh.fund x hφ ((IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).2 ⟨z, hz.symm⟩)
  exact ⟨q, by rw [qB_eq]; exact hq.symm⟩

theorem base_fs_surj (l : ℕ) [Fact l.Prime] : ∀ z : BdR l, ∃ x, φ l x = x ∧ ι l x - z ∈ Plus l := by
  intro z
  obtain ⟨x, hφ, c, hc⟩ := PositivityTheory.LocInh.fund_onto z
  exact ⟨x, hφ, RingHom.mem_range.2 ⟨c, by rw [ι_eq]; exact hc.symm⟩⟩

end period_ring_base
