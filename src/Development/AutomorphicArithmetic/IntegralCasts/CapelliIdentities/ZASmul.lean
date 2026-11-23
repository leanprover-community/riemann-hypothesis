module

public import GroundTheory.PAdicHodge.BdRAlg
public import GroundTheory.PAdicHodge.FactorizationFactorialLe
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Acris :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.ACris.ACris ℂ_[l] l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Ainf :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.AInf ℂ_[l] l

noncomputable def UpperTheory.Reformulated.B.Qi53.zA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → ℤ_[l] →+* UpperTheory.Reformulated.B.Qi53.Acris l :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi53.Ainf l) (UpperTheory.Reformulated.B.Qi53.Acris l)).comp
        (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt l)

theorem UpperTheory.Reformulated.B.Qi53.zA_smul.{u_1} :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {N : Type u_1} [inst_1 : AddCommGroup N]
      [inst_2 : _root_.Module (UpperTheory.Reformulated.B.Qi53.Acris l) N] (n : ℕ),
      (∀ (y : N), (↑l : UpperTheory.Reformulated.B.Qi53.Acris l) ^ n • y = (0 : N)) →
        ∀ (z : ℤ_[l]) (y : N),
          (UpperTheory.Reformulated.B.Qi53.zA l : ℤ_[l] → UpperTheory.Reformulated.B.Qi53.Acris l) z • y =
            ((PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) z).val • y := by
  intro l _ N _ _ n h z y
  have hz : z - (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := by
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : Nat.Prime l).ne_zero⟩
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hz
  obtain ⟨w, hw⟩ := hz
  have hz' : z = (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by
    rw [← hw]; ring
  generalize (PadicInt.toZModPow n z).val = m at hz' ⊢
  rw [hz', map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_smul, mul_smul, h, add_zero,
    Nat.cast_smul_eq_nsmul]
