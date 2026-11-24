module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallSubgroup
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic.Bound
public import Mathlib.Topology.MetricSpace.ProperSpace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaE
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedean, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruence, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruence, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem exists_tExp_eq_indicator (b : Fin n → ℤ) (hb : Antitone b) :
    ∃ i : Fin (n + 2), tExp n i = fun j => if 0 < b j then 1 else 0 := by
  classical
  have hex : ∃ i : ℕ, i = n ∨ ∃ h : i < n, b ⟨i, h⟩ ≤ 0 := ⟨n, Or.inl rfl⟩
  have hle : Nat.find hex ≤ n := Nat.find_min' hex (Or.inl rfl)
  refine ⟨⟨Nat.find hex, by omega⟩, ?_⟩
  funext j
  have hne : Nat.find hex ≠ n + 1 := by omega
  simp only [tExp, hne, if_false]
  by_cases hj : (j : ℕ) < Nat.find hex
  · have hnot := Nat.find_min hex hj
    have hpos : 0 < b j := by
      by_contra hcon
      exact hnot (Or.inr ⟨j.2, not_lt.mp hcon⟩)
    rw [if_pos hj, if_pos hpos]
  · have hspec := Nat.find_spec hex
    have hnpos : ¬ 0 < b j := by
      rcases hspec with h | ⟨h, h'⟩
      · have := j.2
        omega
      · have hmono : b j ≤ b ⟨Nat.find hex, h⟩ := hb (by
          rw [Fin.le_def]
          exact not_lt.mp hj)
        omega
    rw [if_neg hj, if_neg hnpos]

theorem dPow_mem_closure_of_nonneg (p : Lˣ) (N : ℕ) :
    ∀ b : Fin n → ℤ, Antitone b → (∀ j, 0 ≤ b j) → (∀ j, b j ≤ N) →
      dPow p b ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction N with
  | zero =>
    intro b _ h0 hN
    have hb : b = 0 := by
      funext j
      have h1 := h0 j
      have h2 := hN j
      simp only [Nat.cast_zero] at h2
      simp only [Pi.zero_apply]
      omega
    rw [hb, dPow_zero]
    exact Submonoid.one_mem _
  | succ N ih =>
    intro b hb h0 hN
    obtain ⟨i, hi⟩ := exists_tExp_eq_indicator b hb
    have hdecomp : b = (fun j => b j - if 0 < b j then 1 else 0) + tExp n i := by
      rw [hi]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_ ?_) (Submonoid.subset_closure ⟨i, rfl⟩)
    · intro x y hxy
      have hm := hb hxy
      have hx := h0 x
      have hy := h0 y
      show (b y - if 0 < b y then 1 else 0) ≤ (b x - if 0 < b x then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      show 0 ≤ (b j - if 0 < b j then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      have h2 := hN j
      push_cast at h2
      show (b j - if 0 < b j then 1 else 0) ≤ (N : ℤ)
      split_ifs <;> omega

theorem dPow_mem_closure_of_ge (p : Lˣ) (C : ℕ) :
    ∀ a : Fin n → ℤ, Antitone a → (∀ j, -(C : ℤ) ≤ a j) →
      dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction C with
  | zero =>
    intro a ha h0
    have hbd : ∀ j, a j ≤ ((∑ k, (a k).natAbs : ℕ) : ℤ) := by
      intro j
      have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
        Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      omega
    refine dPow_mem_closure_of_nonneg p _ a ha (fun j => ?_) hbd
    have := h0 j
    simpa using this
  | succ C ih =>
    intro a ha h0
    have hlast : tExp n (Fin.last (n + 1)) = fun _ => -1 := by
      funext j
      simp [tExp]
    have hdecomp : a = (fun j => a j + 1) + tExp n (Fin.last (n + 1)) := by
      rw [hlast]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_)
      (Submonoid.subset_closure ⟨Fin.last (n + 1), rfl⟩)
    · intro x y hxy
      have := ha hxy
      show a y + 1 ≤ a x + 1
      omega
    · intro j
      have := h0 j
      push_cast at this
      show -(C : ℤ) ≤ a j + 1
      omega

theorem dPow_antitone_mem_closure (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (p : Lˣ) (a : Fin n → ℤ) (ha : Antitone a) :
    dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  refine dPow_mem_closure_of_ge p (∑ k, (a k).natAbs) a ha (fun j => ?_)
  have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
    Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedean =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedean", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallSubgroup\npublic import Mathlib.RingTheory.DiscreteValuationRing.Basic\npublic import Mathlib.Tactic.Bound\npublic import Mathlib.Topology.MetricSpace.ProperSpace\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.UnitBall

variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]

noncomputable def ball : ValuationSubring L :=
  by apply _root_.UpperTheory.Reformulated.B.BallSubgroup.ball

variable {L}

theorem mem_ball {x : L} : x ∈ ball L ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem isUnit_of_norm_eq_one {x : ball L} (h : ‖(x : L)‖ = 1) : IsUnit x := by
  have hx : (x : L) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact zero_ne_one h
  have hi : (x : L)⁻¹ ∈ ball L := by
    rw [mem_ball, norm_inv, h, inv_one]
  refine IsUnit.of_mul_eq_one ⟨(x : L)⁻¹, hi⟩ ?_
  apply Subtype.ext
  simp [hx]

theorem norm_eq_one_of_isUnit {x : ball L} (h : IsUnit x) : ‖(x : L)‖ = 1 := by
  obtain ⟨y, hy⟩ := h.exists_right_inv
  have h1 : (x : L) * (y : L) = 1 := by
    have := congrArg (Subtype.val) hy
    simpa using this
  have h2 : ‖(x : L)‖ * ‖(y : L)‖ = 1 := by
    rw [← norm_mul, h1, norm_one]
  have hx : ‖(x : L)‖ ≤ 1 := x.2
  have hy' : ‖(y : L)‖ ≤ 1 := y.2
  nlinarith [norm_nonneg (x : L), norm_nonneg (y : L)]

variable {p : Lˣ}

theorem norm_unif_pos (p : Lˣ) : 0 < ‖(p : L)‖ := norm_pos_iff.2 p.ne_zero

theorem exists_nat_norm (hp : IsUnif p) {x : L} (hx : x ≠ 0) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, ‖x‖ = ‖(p : L)‖ ^ m := by
  obtain ⟨a, ha⟩ := hp.2 x hx
  have h0 := norm_unif_pos p
  have hnn : 0 ≤ a := by
    by_contra hneg
    have hlt : a < 0 := not_le.1 hneg
    have : 1 < ‖(p : L)‖ ^ a := one_lt_zpow_of_neg₀ h0 hp.1 hlt
    linarith
  refine ⟨a.toNat, ?_⟩
  rw [ha, ← zpow_natCast, Int.toNat_of_nonneg hnn]

def unif (hp : IsUnif p) : ball L := ⟨p, hp.1.le⟩

theorem unif_coe (hp : IsUnif p) : ((unif hp : ball L) : L) = p := rfl

theorem irreducible_unif (hp : IsUnif p) : Irreducible (unif hp) := by
  have h0 := norm_unif_pos p
  refine ⟨fun h => ?_, ?_⟩
  · have := norm_eq_one_of_isUnit h
    rw [unif_coe] at this
    exact absurd this hp.1.ne
  · intro a b hab
    have hab' : (p : L) = (a : L) * (b : L) := by
      have := congrArg (Subtype.val) hab
      simpa [unif_coe] using this
    have ha0 : (a : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, zero_mul])
    have hb0 : (b : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, mul_zero])
    obtain ⟨i, hi⟩ := exists_nat_norm hp ha0 a.2
    obtain ⟨j, hj⟩ := exists_nat_norm hp hb0 b.2
    have hn : ‖(p : L)‖ ^ 1 = ‖(p : L)‖ ^ (i + j) := by
      rw [pow_one, pow_add, ← hi, ← hj, ← norm_mul, ← hab']
    have hij : 1 = i + j := pow_right_injective₀ h0 hp.1.ne hn
    rcases Nat.eq_zero_or_pos i with h | h
    · left
      apply isUnit_of_norm_eq_one
      rw [hi, h, pow_zero]
    · right
      have : j = 0 := by omega
      apply isUnit_of_norm_eq_one
      rw [hj, this, pow_zero]

theorem isDVR (hp : IsUnif p) : IsDiscreteValuationRing (ball L) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif hp, irreducible_unif hp, ?_⟩
  intro x hx
  have hx0 : (x : L) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨m, hm⟩ := exists_nat_norm hp hx0 x.2
  have h0 := norm_unif_pos p
  have hpm : (p : L) ^ m ≠ 0 := pow_ne_zero _ p.ne_zero
  have hq : ‖(x : L) / (p : L) ^ m‖ = 1 := by
    rw [norm_div, norm_pow, hm]
    exact div_self (pow_ne_zero _ h0.ne')
  let q : ball L := ⟨(x : L) / (p : L) ^ m, hq.le⟩
  obtain ⟨u, hu⟩ := isUnit_of_norm_eq_one (x := q) hq
  refine ⟨m, u, ?_⟩
  apply Subtype.ext
  have hu' : ((u : ball L) : L) = (x : L) / (p : L) ^ m := by rw [hu]
  change ((unif hp : ball L) : L) ^ m * ((u : ball L) : L) = (x : L)
  rw [hu', unif_coe]
  field_simp

theorem map_mem_congK (n : ℕ) (U : GL (Fin n) (ball L)) :
    Matrix.GeneralLinearGroup.map (algebraMap (ball L) L) U ∈ congK L n 1 zero_le_one le_rfl := by
  have key : ∀ (A : Matrix (Fin n) (Fin n) (ball L)) (i j : Fin n),
      ‖(A.map (algebraMap (ball L) L) - 1) i j‖ ≤ 1 := by
    intro A i j
    rw [Matrix.sub_apply, Matrix.map_apply, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (A i j).2 ?_)
    rw [norm_neg, Matrix.one_apply]
    split_ifs <;> simp
  intro i j
  refine ⟨key _ i j, ?_⟩
  rw [← map_inv]
  exact key _ i j

end GlobalTheory.CompanionTheory.CartGL.UnitBall

namespace GlobalTheory.CompanionTheory.CartGL


open UnitBall in
theorem cartan_unitBall (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (p : Lˣ) (hp : IsUnif p) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ congK L n 1 zero_le_one le_rfl,
      ∃ k₂ ∈ congK L n 1 zero_le_one le_rfl, g = k₁ * dPow p a * k₂ := by
  haveI := isDVR hp
  have hdet : IsUnit (g : Matrix (Fin n) (Fin n) L).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  obtain ⟨u, v, a, hu, hv, ha, hg⟩ := GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists (ball L) L n (unif hp)
    (irreducible_unif hp) (g : Matrix (Fin n) (Fin n) L) hdet
  obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det u).2 hu
  obtain ⟨V, rfl⟩ := (Matrix.isUnit_iff_isUnit_det v).2 hv
  refine ⟨a, ha, _, map_mem_congK n U, _, map_mem_congK n V, ?_⟩
  apply Units.ext
  rw [hg, Units.val_mul, Units.val_mul, dPow_val]
  have hd : (Matrix.diagonal fun i => (algebraMap (ball L) L (unif hp)) ^ (a i)) =
      Matrix.diagonal fun i => ((p ^ a i : Lˣ) : L) := by
    congr 1
    funext i
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  rw [hd]
  rfl

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedean =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets", "h": "module\n\npublic import Mathlib.Algebra.Group.Subgroup.Defs\npublic import Mathlib.Topology.Algebra.Group.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Topology.Compactness.Compact\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.CompanionTheory.CosetCover

theorem exists_finite_coset_cover :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G),
      IsCompact (K₀ : Set G) → IsOpen (K : Set G) →
        ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  intro G _ _ _ K₀ K hK₀ hK
  classical
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover
    (fun g : K₀ => (fun x => x * (g : G)⁻¹) ⁻¹' (K : Set G))
    (fun g => hK.preimage (continuous_mul_const _))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : K₀) : G), fun i => (t.equivFin.symm i : K₀).2,
    fun g hg => ?_⟩
  obtain ⟨a, ha, hga⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨t.equivFin ⟨a, ha⟩, g * (a : G)⁻¹, hga, ?_⟩
  simp

end GlobalTheory.CompanionTheory.CosetCover
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\npublic import Mathlib.Topology.Instances.Matrix\npublic import Mathlib.Topology.MetricSpace.ProperSpace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isCompact_entryBall (L : Type) [NontriviallyNormedField L] [ProperSpace L] (n : ℕ) (r : ℝ) :
    IsCompact {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} := by
  have h : IsCompact (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
      Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  have e : {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} =
      (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
        Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) := by
    ext M
    constructor
    · intro hM i _ j _
      have := hM i j
      rw [Matrix.sub_apply] at this
      exact mem_closedBall_iff_norm.2 this
    · intro hM i j
      have := mem_closedBall_iff_norm.1 (hM i (Set.mem_univ _) j (Set.mem_univ _))
      rw [Matrix.sub_apply]
      exact this
  rw [e]
  exact h

theorem isCompact_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsCompact (congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  have hS := isCompact_entryBall L n r
  have hS' := hS.image MulOpposite.continuous_op
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  have e : (congK L n r h0 h1 : Set (GL (Fin n) L)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) L) ⁻¹'
        ({M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} ×ˢ
          (MulOpposite.op '' {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r})) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      Set.mem_image, Set.mem_setOf_eq, MulOpposite.op_inj, exists_eq_right]
    exact ⟨fun hk => ⟨fun i j => (hk i j).1, fun i j => (hk i j).2⟩,
      fun hk i j => ⟨hk.1 i j, hk.2 i j⟩⟩
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\npublic import Mathlib.Topology.Instances.Matrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isOpen_congK : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r →
    IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  intro L _ _ n r h0 h1 hr
  have hball : IsOpen (Metric.closedBall (0 : L) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr.ne'
  have hval : Continuous fun k : GL (Fin n) L => (k : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val
  have hinv : Continuous fun k : GL (Fin n) L => ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val.comp continuous_inv
  have hset : (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ((fun k : GL (Fin n) L => ((k : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r ∩
          (fun k : GL (Fin n) L =>
            (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
      mem_closedBall_zero_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hval.sub continuous_const)
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hinv.sub continuous_const)

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\npublic import Mathlib.Tactic.Bound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.Normal

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem entry_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖(A - 1) i j‖ ≤ 1) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by
  have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) ?_)
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

theorem entry_conj {C D X : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hC : ∀ i j, ‖C i j‖ ≤ 1) (hD : ∀ i j, ‖D i j‖ ≤ 1) (hCD : C * D = 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ r) (i j : Fin n) : ‖(C * X * D - 1) i j‖ ≤ r := by
  have e : C * X * D - 1 = C * (X - 1) * D := by
    rw [mul_sub, sub_mul, mul_one, hCD]
  rw [e]
  have h := entry_mul (mul_nonneg zero_le_one h0) zero_le_one
    (entry_mul zero_le_one h0 hC hX) hD i j
  simpa using h

theorem conj_mem_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L)
    (hc : c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (hx : x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) :
    c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
  have hC : ∀ i j, ‖((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).1
  have hD : ∀ i j, ‖(((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).2
  have hCD : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  intro i j
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).1) i j
  · have e : (c * x * c⁻¹)⁻¹ = c * x⁻¹ * c⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).2) i j

end GlobalTheory.CompanionTheory.CartGL.Normal
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\npublic import Mathlib.Topology.Instances.Matrix\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix Topology

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_pi_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Fin n → Fin n → L)} {x : Fin n → Fin n → L} (hA : A ∈ 𝓝 x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin n → Fin n → L, (∀ i j, ‖y i j - x i j‖ ≤ ε) → y ∈ A := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨ε / 2, half_pos hε, fun y hy => hball ?_⟩
  have hd : dist y x ≤ ε / 2 := by
    rw [dist_pi_le_iff (half_pos hε).le]
    intro i
    rw [dist_pi_le_iff (half_pos hε).le]
    intro j
    rw [dist_eq_norm]
    exact hy i j
  rw [Metric.mem_ball]
  linarith

theorem exists_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Matrix (Fin n) (Fin n) L)} (hA : A ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) L,
      (∀ i j, ‖(M - 1) i j‖ ≤ ε) → M ∈ A := by
  obtain ⟨ε, hε, h⟩ := exists_pi_entry_box (x := (1 : Matrix (Fin n) (Fin n) L)) hA
  refine ⟨ε, hε, fun M hM => h M fun i j => ?_⟩
  have := hM i j
  rwa [Matrix.sub_apply] at this

theorem congK_cofinal (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (U : Set (GL (Fin n) L)) (hU : IsOpen U) (h1U : (1 : GL (Fin n) L) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε →
      (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  have hU1 : U ∈ 𝓝 (1 : GL (Fin n) L) := hU.mem_nhds h1U
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap, map_one] at hU1
  obtain ⟨V, hV, hVU⟩ := hU1
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    (mem_nhds_prod_iff (x := (1 : Matrix (Fin n) (Fin n) L)) (y := MulOpposite.op 1)).1 hV
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_entry_box hA
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_entry_box hB'
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r h0 h1 hr k hk => hVU (hAB ⟨?_, ?_⟩)⟩
  · exact h₁ _ fun i j => ((hk i j).1.trans hr).trans (min_le_left _ _)
  · exact h₂ _ fun i j => ((hk i j).2.trans hr).trans (min_le_right _ _)

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruence =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruence", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.Lower

theorem conj_entry {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
    (p : Lˣ) (a : Fin n → ℤ) (w : GL (Fin n) L) (i j : Fin n) :
    (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i j * ((p ^ a j : Lˣ) : L) := by
  have h : (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  rw [Units.val_mul, Units.val_mul, h, GlobalTheory.CompanionTheory.CartGL.dPow_val, mul_diagonal, diagonal_mul]

theorem norm_conj_le {L : Type} [NontriviallyNormedField L] (p : Lˣ) (hp : ‖(p : L)‖ < 1)
    {b c : ℤ} (hbc : b ≤ c) (x : L) :
    ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ ≤ ‖x‖ := by
  have hp0 : (0 : ℝ) < ‖(p : L)‖ := norm_pos_iff.mpr p.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℕ, c = b + m := ⟨(c - b).toNat, by omega⟩
  have e : ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ = ‖x‖ * ‖(p : L)‖ ^ m := by
    rw [norm_mul, norm_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow,
      norm_zpow, hm, zpow_add₀ hp0.ne', _root_.zpow_neg, zpow_natCast]
    have : ‖(p : L)‖ ^ b ≠ 0 := (zpow_pos hp0 b).ne'
    field_simp
  rw [e]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hp0.le hp.le)

theorem conj_lower_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (w : GL (Fin n) L), (∀ i j, i < j → (w : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((w : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖((((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r w hl hr i j
  rw [Matrix.sub_apply, conj_entry]
  rcases lt_trichotomy i j with h | h | h
  · have h0 := hr i j
    rw [Matrix.sub_apply, hl i j h, Matrix.one_apply_ne h.ne] at h0
    rw [hl i j h, Matrix.one_apply_ne h.ne]
    simpa using h0
  · subst h
    have hne : ((p ^ (-a i) : Lˣ) : L) * ((p ^ a i : Lˣ) : L) = 1 := by
      rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]
    have e : ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i i * ((p ^ a i : Lˣ) : L) =
        (w : Matrix (Fin n) (Fin n) L) i i := by
      rw [mul_right_comm, hne, one_mul]
    rw [e]
    simpa [Matrix.sub_apply] using hr i i
  · have h0 := hr i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne h.ne', sub_zero] at h0
    rw [Matrix.one_apply_ne h.ne', sub_zero]
    exact (norm_conj_le p hp (ha h.le) _).trans h0

end GlobalTheory.CompanionTheory.CartGL.Lower
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruence =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruence =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruence", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem conj_upper_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (u : GL (Fin n) L), (∀ i j, j < i → (u : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((u : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖(((GlobalTheory.CompanionTheory.CartGL.dPow p a * u * (GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r u hlow hr i j
  have hinv : (((dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  have hent : ((dPow p a * u * (dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (a i - a j) : Lˣ) : L) * (u : Matrix (Fin n) (Fin n) L) i j := by
    rw [Units.val_mul, Units.val_mul, dPow_val, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul,
      sub_eq_add_neg, _root_.zpow_add, Units.val_mul]
    ring
  rw [Matrix.sub_apply, hent]
  have hri := hr i j
  rw [Matrix.sub_apply] at hri
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : i ≠ j := ne_of_lt hij
    rw [Matrix.one_apply_ne hne] at hri ⊢
    rw [sub_zero] at hri ⊢
    have hexp : 0 ≤ a i - a j := sub_nonneg.mpr (ha hij.le)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hexp
    have hpow : ‖((p ^ (a i - a j) : Lˣ) : L)‖ ≤ 1 := by
      rw [hm, zpow_natCast, Units.val_pow_eq_pow_val, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hp.le
    rw [norm_mul]
    calc _ ≤ 1 * ‖(u : Matrix (Fin n) (Fin n) L) i j‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ r := hri
  · subst hij
    simpa using hri
  · rw [hlow i j hij, mul_zero]
    rw [hlow i j hij] at hri
    exact hri

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruence =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem tExp_antitone (n : ℕ) (i : Fin (n + 2)) : Antitone (tExp n i) := by
  intro j k hjk
  have hjk' : (j : ℕ) ≤ (k : ℕ) := hjk
  unfold tExp
  by_cases h : (i : ℕ) = n + 1
  · simp [h]
  · simp only [h, if_false]
    by_cases hk : (k : ℕ) < i
    · have hj : (j : ℕ) < i := lt_of_le_of_lt hjk' hk
      simp [hj, hk]
    · by_cases hj : (j : ℕ) < i <;> simp [hj, hk]

theorem closure_tGen_antitone (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (p : Lˣ) (s : GL (Fin n) L)
    (hs : s ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L))) :
    ∃ a : Fin n → ℤ, Antitone a ∧ s = dPow p a := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨tExp n i, tExp_antitone n i, rfl⟩
  | one => exact ⟨0, fun _ _ _ => le_rfl, (dPow_zero p).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, ha.add hb, (dPow_add p a b).symm⟩

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\npublic import Mathlib.Topology.MetricSpace.ProperSpace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_isUnif : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L],
    ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  intro L _ _ _
  obtain ⟨x₀, h0, h1⟩ := NormedField.exists_norm_lt_one L
  have hc : IsCompact (Metric.ball (0 : L) 1) :=
    Metric.isCompact_of_isClosed_isBounded (IsUltrametricDist.isClosed_ball 0 1) Metric.isBounded_ball
  have hx : x₀ ∈ Metric.ball (0 : L) 1 := by simpa using h1
  obtain ⟨p, hp, hmax⟩ := hc.exists_isMaxOn ⟨x₀, hx⟩ continuous_norm.continuousOn
  have hmax' : ∀ w : L, ‖w‖ < 1 → ‖w‖ ≤ ‖p‖ := fun w hw =>
    isMaxOn_iff.mp hmax w (by simpa using hw)
  have hp1 : ‖p‖ < 1 := by simpa using hp
  have hp0 : 0 < ‖p‖ := h0.trans_le (hmax' x₀ h1)
  have hpne : p ≠ 0 := norm_pos_iff.mp hp0
  refine ⟨Units.mk0 p hpne, hp1, fun x hx0 => ?_⟩
  rw [Units.val_mk0]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy : 1 < ‖p‖⁻¹ := (one_lt_inv₀ hp0).mpr hp1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hxpos hy
  set w : L := p ^ (-n) * x⁻¹ with hw
  have hwn : ‖w‖ = ‖p‖⁻¹ ^ n / ‖x‖ := by
    rw [hw, norm_mul, norm_inv, norm_zpow, _root_.inv_zpow', div_eq_mul_inv]
  have hle : ‖w‖ ≤ 1 := by
    rw [hwn]; exact (div_le_one hxpos).mpr hn1
  have hgt : ‖p‖ < ‖w‖ := by
    rw [hwn, lt_div_iff₀ hxpos]
    have : ‖x‖ < ‖p‖⁻¹ ^ n * ‖p‖⁻¹ := by rwa [zpow_add_one₀ (inv_pos.mpr hp0).ne'] at hn2
    calc ‖p‖ * ‖x‖ < ‖p‖ * (‖p‖⁻¹ ^ n * ‖p‖⁻¹) := mul_lt_mul_of_pos_left this hp0
      _ = ‖p‖⁻¹ ^ n := by field_simp
  have heq : ‖w‖ = 1 := by
    by_contra hne
    exact absurd (hmax' w (lt_of_le_of_ne hle hne)) (not_le.mpr hgt)
  refine ⟨-n, ?_⟩
  rw [hwn, div_eq_one_iff_eq hxpos.ne'] at heq
  rw [← heq, _root_.inv_zpow']

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaE\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

section SlopeTestRemainingChoices

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem norm_det_sub_det_le {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (hAB : ∀ i j, ‖(A - B) i j‖ ≤ r) :
    ‖A.det - B.det‖ ≤ r := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun σ _ => ?_
  rw [← smul_sub]
  have h := _root_.Bl.FirstLemmaE.goal1 Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i) h0
    (fun i => hA _ _) (fun i => hB _ _) (fun i => by simpa using hAB (σ i) i)
  have h' : ‖∏ i, B (σ i) i - ∏ i, A (σ i) i‖ ≤ r := by
    rw [norm_sub_rev]
    exact h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs, Units.smul_def] using h
  · simpa [hs, Units.smul_def] using h'

theorem norm_det_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have h : ‖∏ i, A (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs, Units.smul_def] using h

theorem norm_one_entry_le (i j : Fin n) : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

theorem norm_adjugate_entry_le {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : Fin n) :
    ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases h' : b = i
    · simp [h']
    · simp [Pi.single_eq_of_ne h']
  · rw [Matrix.updateRow_ne h]
    exact hA a b

end SlopeTestRemainingChoices

theorem exists_mem_congK_of_entries : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L,
    (∀ i j, ‖(A - 1) i j‖ ≤ r) →
    ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  intro L _ _ n r h0 h1 hr A hA
  have hA1 : ∀ i j, ‖A i j‖ ≤ 1 := by
    intro i j
    have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((hA i j).trans h1) (norm_one_entry_le i j))
  have hd : ‖A.det - 1‖ ≤ r := by
    have := norm_det_sub_det_le h0 hA1 norm_one_entry_le hA
    rwa [Matrix.det_one] at this
  have hd1 : 1 ≤ ‖A.det‖ := by
    have e : (1 : L) = A.det + -(A.det - 1) := by ring
    have h2 : ‖(1 : L)‖ ≤ max ‖A.det‖ ‖A.det - 1‖ := by
      conv_lhs => rw [e]
      rw [← norm_neg (A.det - 1)]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [norm_one] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · linarith
  have hne : A.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have hinv : ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by
    intro i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact mul_le_one₀ (inv_le_one_of_one_le₀ hd1) (norm_nonneg _) (norm_adjugate_entry_le hA1 i j)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  have hk : ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hne : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = A := rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hne, ?_, hk⟩
  rw [mem_congK]
  intro i j
  refine ⟨by rw [hk]; exact hA i j, ?_⟩
  rw [Matrix.coe_units_inv, hk]
  have e : A⁻¹ - 1 = -(A⁻¹ * (A - 1)) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul A hu, Matrix.mul_one]
    abel
  rw [e, Matrix.neg_apply, norm_neg]
  simpa using entry_mul zero_le_one h0 hinv hA i j

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization", "h": "module\n\npublic import Mathlib.Analysis.Normed.Field.Basic\npublic import Mathlib.Data.Matrix.Mul\npublic import Mathlib.Topology.MetricSpace.Ultra.Basic\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}





theorem iwahori_factorisation (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r < 1) (A : Matrix (Fin n) (Fin n) L) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) :
    ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
      (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  _root_.UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor n r h0 h1 A hA

end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL", "h": "module\n\npublic import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid\npublic import Mathlib.Tactic.Bound\npublic import Mathlib.Topology.MetricSpace.ProperSpace\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedean\npublic import Mathlib.Algebra.Group.Subgroup.Defs\npublic import Mathlib.Topology.Algebra.Group.Defs\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets\npublic import Mathlib.Topology.Instances.Matrix\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruence\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruence\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup\npublic import Mathlib.Analysis.Normed.Field.Basic\npublic import Mathlib.Data.Matrix.Mul\npublic import Mathlib.Topology.MetricSpace.Ultra.Basic\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.Fl Matrix
namespace GlobalTheory.CompanionTheory.CartGL

theorem stCartanGL : StCartanGL := by
  unfold CompanionTheory.Rg.Fl.StCartanGL CompanionTheory.Rg.Fl.HasCartan
  intro L _ _ _ n U hU
  obtain ⟨p, hp⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.exists_isUnif L
  have hp1 : ‖(p : L)‖ < 1 := by
    unfold GlobalTheory.CompanionTheory.CartGL.IsUnif at hp
    exact hp.1
  obtain ⟨ε, hε, hεU⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.congK_cofinal L n (U : Set (GL (Fin n) L)) hU U.one_mem
  obtain ⟨r, hr0, hr1, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ≤ ε :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), min_le_left _ _⟩
  have h0 : 0 ≤ r := hr0.le
  have h1 : r ≤ 1 := hr1.le
  refine ⟨GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, fun x hx => hεU r h0 h1 hrε hx,
    _root_.GlobalTheory.CompanionTheory.CartGL.isOpen_congK L n r h0 h1 hr0, _root_.GlobalTheory.CompanionTheory.CartGL.isCompact_congK L n r h0 h1, ?_⟩
  obtain ⟨d, c, hc, hcK⟩ := _root_.GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover (GL (Fin n) L) (GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) (_root_.GlobalTheory.CompanionTheory.CartGL.isCompact_congK L n 1 zero_le_one le_rfl) (_root_.GlobalTheory.CompanionTheory.CartGL.isOpen_congK L n r h0 h1 hr0)
  refine ⟨d, n + 2, ?_⟩
  unfold CompanionTheory.Rg.Fl.IsCartan
  refine ⟨c, GlobalTheory.CompanionTheory.CartGL.tGen p, ?_, ?_, ?_, ?_⟩
  · intro i k
    constructor
    · intro hk
      exact _root_.GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK L n r h0 h1 (c i) k (hc i) hk
    · intro hk
      have h2 := _root_.GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK L n r h0 h1 (c i)⁻¹ _ (Subgroup.inv_mem _ (hc i)) hk
      have e : (c i)⁻¹ * (c i * k * (c i)⁻¹) * (c i)⁻¹⁻¹ = k := by group
      rwa [e] at h2
  · intro i j
    show GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) =
      GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i)
    rw [← GlobalTheory.CompanionTheory.CartGL.dPow_add, ← GlobalTheory.CompanionTheory.CartGL.dPow_add, add_comm]
  · intro g
    obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, rfl⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.cartan_unitBall L n p hp g
    obtain ⟨i, κ₁, hκ₁, rfl⟩ := hcK k₁ hk₁
    obtain ⟨j, κ₂, hκ₂, rfl⟩ := hcK k₂ hk₂
    refine ⟨i, j, GlobalTheory.CompanionTheory.CartGL.dPow p a, _root_.GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure L n p a ha, κ₁, hκ₁, (c j)⁻¹ * κ₂ * c j, ?_, ?_⟩
    · have h2 := _root_.GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK L n r h0 h1 (c j)⁻¹ κ₂ (Subgroup.inv_mem _ (hc j)) hκ₂
      rwa [inv_inv] at h2
    · group
  · intro s hs s' hs' k hk
    obtain ⟨a₁, ha₁, rfl⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone L n p s hs
    obtain ⟨a₂, ha₂, rfl⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone L n p s' hs'
    have hkA : ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := fun i j =>
      (GlobalTheory.CompanionTheory.CartGL.mem_congK.mp hk i j).1
    obtain ⟨Um, Wm, hUl, hWu, hUr, hWr, hUW⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation L n r h0 hr1 (k : Matrix (Fin n) (Fin n) L) hkA
    obtain ⟨kU, -, hkUv⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries L n r h0 h1 hr1 Um hUr
    obtain ⟨kW, -, hkWv⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries L n r h0 h1 hr1 Wm hWr
    have hk_eq : k = kU * kW := Units.ext (by rw [Units.val_mul, hkUv, hkWv, hUW])
    have hA : GlobalTheory.CompanionTheory.CartGL.dPow p a₁ * kU * (GlobalTheory.CompanionTheory.CartGL.dPow p a₁)⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := _root_.GlobalTheory.CompanionTheory.CartGL.conj_upper_contract L n p hp1 a₁ ha₁ r kU (fun i j hij => by rw [hkUv]; exact hUl i j hij)
        (fun i j => by rw [hkUv]; exact hUr i j)
      obtain ⟨k', hk', hk'v⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    have hB : (GlobalTheory.CompanionTheory.CartGL.dPow p a₂)⁻¹ * kW * GlobalTheory.CompanionTheory.CartGL.dPow p a₂ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := _root_.GlobalTheory.CompanionTheory.CartGL.Lower.conj_lower_contract L n p hp1 a₂ ha₂ r kW (fun i j hij => by rw [hkWv]; exact hWu i j hij)
        (fun i j => by rw [hkWv]; exact hWr i j)
      obtain ⟨k', hk', hk'v⟩ := _root_.GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    refine ⟨_, hA, _, hB, ?_⟩
    rw [hk_eq]
    group

end GlobalTheory.CompanionTheory.CartGL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL =====
