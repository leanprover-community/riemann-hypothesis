module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
public import Mathlib.LinearAlgebra.Dual.Lemmas
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.PiTensorProduct

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLower, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper, CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLower =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLower", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.Unitary

variable {E ι : Type} [Ring E] [Fintype ι]

theorem piece_mul_mul {P : ι → E} (hP : IsPieces P) (x y : E) (i j : ι) :
    P i * (x * y) * P j = ∑ k, (P i * x * P k) * (P k * y * P j) := by
  have h : x * y = ∑ k, x * P k * y := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP.sum, mul_one]
  rw [h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hP.idem k
  calc P i * (x * P k * y) * P j = P i * x * P k * y * P j := by simp only [mul_assoc]
    _ = P i * x * (P k * P k) * y * P j := by rw [hk]
    _ = _ := by simp only [mul_assoc]

theorem upper_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsUpper wt P x) (hy : IsUpper wt P y) : IsUpper wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt k) (wt i) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_lt_of_le hij h), mul_zero]

theorem lower_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsLower wt P x) (hy : IsLower wt P y) : IsLower wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt i) (wt k) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_le_of_lt h hij), mul_zero]

theorem diag_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLower wt P x) (hy : IsLower wt P y) (i : ι) :
    P i * (x * y) * P i = (P i * x * P i) * (P i * y * P i) := by
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_trichotomy (wt i) (wt k) with h | h | h
  · rw [hx i k h, zero_mul]
  · exact absurd (hw h).symm hk
  · rw [hy k i h, mul_zero]

theorem lowerUni_mul {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLowerUni wt P x) (hy : IsLowerUni wt P y) : IsLowerUni wt P (x * y) :=
  ⟨lower_mul hP hx.1 hy.1, fun i => by
    rw [diag_mul hP hw hx.1 hy.1, hx.2, hy.2, hP.idem]⟩

theorem lowerUni_of_inv {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {b b' : E} (hb : IsLowerUni wt P b) (hb' : IsLower wt P b') (h : b * b' = 1) :
    IsLowerUni wt P b' := by
  refine ⟨hb', fun i => ?_⟩
  have h1 := diag_mul hP hw hb.1 hb' i
  rw [h, mul_one, hP.idem, hb.2] at h1
  calc P i * b' * P i = P i * (P i * b' * P i) := by simp only [← mul_assoc, hP.idem]
    _ = P i := h1.symm

theorem eq_one_of_upper_lowerUni {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P)
    (hw : Function.Injective wt) {c : E} (hu : IsUpper wt P c) (hl : IsLowerUni wt P c) :
    c = 1 := by
  have h : c = ∑ i, ∑ j, P i * c * P j := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hP.sum, mul_one, one_mul]
  rw [h, ← hP.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_eq_single i (fun j _ hj => ?_)
    (fun h => absurd (Finset.mem_univ i) h)).trans (hl.2 i)
  rcases lt_trichotomy (wt i) (wt j) with h | h | h
  · exact hl.1 i j h
  · exact absurd (hw h).symm hj
  · exact hu i j h

section Anti

variable {wt : ι → ℕ} {P : ι → E} {rev : ι → ι} {st : E → E}

theorem st_block (hrev : ∀ i, rev (rev i) = i) (hmul : ∀ a b, st (a * b) = st b * st a)
    (hst : ∀ i, st (P i) = P (rev i)) (x : E) (i j : ι) :
    P i * st x * P j = st (P (rev j) * x * P (rev i)) := by
  rw [hmul, hmul, hst, hst, hrev, hrev, mul_assoc]

theorem st_upper (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsUpper wt P x) : IsUpper wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord j i hij), h0]

theorem st_lower (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLower wt P x) : IsLower wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord i j hij), h0]

theorem st_lowerUni (hrev : ∀ i, rev (rev i) = i)
    (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsLowerUni wt P x) :
    IsLowerUni wt P (st x) :=
  ⟨st_lower hrev hord hmul h0 hst hx.1, fun i => by
    rw [st_block hrev hmul hst, hx.2, hst, hrev]⟩

end Anti

theorem st_mul_self_of_factor : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ (rev : ι → ι), (∀ i, rev (rev i) = i) → (∀ i j, wt i < wt j → wt (rev j) < wt (rev i)) → Function.Injective wt → ∀ (st : E → E), (∀ a b, st (a * b) = st b * st a) → st 1 = 1 → st 0 = 0 → (∀ i, st (P i) = P (rev i)) → (∀ a a' : E, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a') → (∀ b b' : E, b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b') → ∀ a a' b b' : E, a * a' = 1 → a' * a = 1 → b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b → st (a * b) * (a * b) = 1 → (a * b) * st (a * b) = 1 → st a * a = 1 ∧ st b * b = 1 := by
  intro E ι _ _ wt P hP rev hrev hord hw st hmul h1 h0 hst hU hL a a' b b' haa' ha'a hbb' hb'b ha hb hs hs'
  have ha'U : IsUpper wt P a' := hU a a' haa' ha'a ha
  have ha2U : IsUpper wt P (st a') := st_upper hrev hord hmul h0 hst ha'U
  have hstb : IsLowerUni wt P (st b) := st_lowerUni hrev hord hmul h0 hst hb

  have e1 : st a * st a' = 1 := by rw [← hmul, ha'a, h1]
  have e2 : st b' * st b = 1 := by rw [← hmul, hbb', h1]
  have e3 : st b * st b' = 1 := by rw [← hmul, hb'b, h1]

  have e4 : st a' * st b' = a * b := by
    have h2 : st (a * b) * (st a' * st b') = 1 := by
      rw [hmul a b, mul_assoc (st b), ← mul_assoc (st a), e1, one_mul, e3]
    calc st a' * st b' = (a * b) * st (a * b) * (st a' * st b') := by rw [hs', one_mul]
      _ = a * b := by rw [mul_assoc, h2, mul_one]
  have e5 : st a' = a * b * st b := by
    rw [← e4, mul_assoc, e2, mul_one]

  have e6 : a' * st a' = b * st b := by
    have h3 : a' * (a * b * st b) = (a' * a) * b * st b := by simp only [mul_assoc]
    rw [e5, h3, ha'a, one_mul]
  have hc : a' * st a' = 1 :=
    eq_one_of_upper_lowerUni hP hw (upper_mul hP ha'U ha2U)
      (e6 ▸ lowerUni_mul hP hw hb hstb)
  have e7 : st a' = a := by
    calc st a' = a * a' * st a' := by rw [haa', one_mul]
      _ = a := by rw [mul_assoc, hc, mul_one]
  have e8 : st b' = b := by
    have : a * st b' = a * b := by rw [← e4, e7]
    calc st b' = a' * a * st b' := by rw [ha'a, one_mul]
      _ = a' * a * b := by rw [mul_assoc, this, mul_assoc]
      _ = b := by rw [ha'a, one_mul]
  rw [e7] at e1
  rw [e8] at e3
  exact ⟨e1, e3⟩

end GlobalTheory.CompanionTheory.Iwahori.Unitary
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLower =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Analysis.Normed.Group.Ultra\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Basic\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.CongUnit

variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]

theorem norm_one_add_of_lt {t : L} (ht : ‖t‖ < 1) : ‖1 + t‖ = 1 := by
  have hne : ‖(1 : L)‖ ≠ ‖t‖ := by rw [norm_one]; exact ht.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
  exact max_eq_left ht.le

theorem exists_coord {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hx : x ≠ 0) :
    ∃ i, (∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖) ∧ b.repr x i ≠ 0 ∧
      ‖b.repr ((1 + g) x) i‖ = ‖b.repr x i‖ := by
  have hne : ∃ j, b.repr x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hx
    have : b.repr x = 0 := by
      ext j
      simpa using hcon j
    simpa using this
  obtain ⟨j₀, hj₀⟩ := hne
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖b.repr x j‖)
    ⟨j₀, Finset.mem_univ _⟩
  have hmax : ∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖ := fun j => hi j (Finset.mem_univ _)
  have hc : b.repr x i ≠ 0 := by
    intro h0
    have := hmax j₀
    rw [h0, norm_zero] at this
    exact hj₀ (norm_le_zero_iff.mp this)
  refine ⟨i, hmax, hc, ?_⟩
  set c := b.repr x i with hcdef
  have hy : c⁻¹ • x ∈ Λ := by
    rw [hb]
    intro j
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hmax j) (norm_nonneg _)
  obtain ⟨z, hz, hgz⟩ := hg _ hy
  have hzi : ‖b.repr z i‖ ≤ 1 := (hb z).1 hz i
  have hval : g x = c • π • z := by
    have h1 : g (c⁻¹ • x) = c⁻¹ • g x := map_smul g _ _
    rw [h1] at hgz
    rw [← hgz, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hGx : b.repr ((1 + g) x) i = c * (1 + π * b.repr z i) := by
    have : (1 + g) x = x + c • π • z := by
      rw [LinearMap.add_apply, Module.End.one_apply, hval]
    rw [this, map_add (f := _), map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, ← hcdef]
    ring
  have ht : ‖π * b.repr z i‖ < 1 := by
    rw [norm_mul]
    calc ‖π‖ * ‖b.repr z i‖ ≤ ‖π‖ * 1 := by gcongr
      _ < 1 := by simpa using hπ
  rw [hGx, norm_mul, norm_one_add_of_lt ht, mul_one]

theorem eq_zero_of_apply {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (h0 : (1 + g) x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨i, -, hc, hn⟩ := exists_coord b hb hπ hg hx
  rw [h0, map_zero, Finsupp.zero_apply, norm_zero] at hn
  exact hc (norm_eq_zero.mp hn.symm)

theorem mem_of_apply_mem {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hG : (1 + g) x ∈ Λ) : x ∈ Λ := by
  by_cases hx : x = 0
  · rw [hx]; exact Λ.zero_mem
  obtain ⟨i, hmax, -, hn⟩ := exists_coord b hb hπ hg hx
  rw [hb]
  intro j
  exact (hmax j).trans (hn ▸ (hb _).1 hG i)

theorem main : ∀ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
    [Module L V] [FiniteDimensional L V] (Λ : AddSubgroup V), IsLat L Λ → ∀ π : L, ‖π‖ < 1 →
    ∀ g ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π, ∃ g' ∈ GlobalTheory.CompanionTheory.Iwahori.congJ Λ π,
      (1 + g) * (1 + g') = 1 ∧ (1 + g') * (1 + g) = 1 := by
  intro L V _ _ _ _ _ Λ hΛ π hπ g hg
  obtain ⟨m, b, hb⟩ := hΛ
  have hker : LinearMap.ker (1 + g) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact eq_zero_of_apply b hb hπ hg hx
  obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_ker_eq_bot (1 + g)).2 hker
  have hGH : (1 + g) * (↑u⁻¹ : Module.End L V) = 1 := by rw [← hu]; exact u.mul_inv
  have hHG : (↑u⁻¹ : Module.End L V) * (1 + g) = 1 := by rw [← hu]; exact u.inv_mul
  set H : Module.End L V := ↑u⁻¹ with hH
  have hGHx : ∀ x, (1 + g) (H x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hGH
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHGx : ∀ x, H ((1 + g) x) = x := fun x => by
    have := congrArg (fun f : Module.End L V => f x) hHG
    simpa only [Module.End.mul_apply, Module.End.one_apply] using this
  have hHmem : ∀ x ∈ Λ, H x ∈ Λ := fun x hx =>
    mem_of_apply_mem b hb hπ hg (by rw [hGHx]; exact hx)
  refine ⟨H - 1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hgy⟩ := hg x hx
    refine ⟨-H y, Λ.neg_mem (hHmem y hy), ?_⟩
    have h1 : H x + H (g x) = x := by
      have := hHGx x
      rwa [LinearMap.add_apply, Module.End.one_apply, map_add] at this
    have h2 : (H - 1) x = H x - x := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [h2, smul_neg, ← map_smul, ← hgy]
    rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, h1, sub_self]
  · rw [add_sub_cancel]; exact hGH
  · rw [add_sub_cancel]; exact hHG

end GlobalTheory.CompanionTheory.Iwahori.CongUnit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists", "h": "module\n\npublic import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich\nimport Mathlib.Algebra.Module.StablyFree.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.Matrix.FiniteDimensional\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.LinearAlgebra.Dual.Lemmas\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem exists_adjoint_herm : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h →
    ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by
  intro L V _ _ _ _ s hs h hh g
  obtain ⟨hadd2, hsmul2, hsymm, hnd⟩ := hh
  have hss := hs.1
  have hadd1 : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y
    rw [hsymm y (x + x'), hadd2, map_add (f := _), ← hsymm, ← hsymm]
  have hsmul1 : ∀ (a : L) x y, h (a • x) y = s a * h x y := by
    intro a x y
    rw [hsymm y (a • x), hsmul2, map_mul, ← hsymm]

  let ψ₀ : V → Module.Dual L V := fun x =>
    { toFun := h x
      map_add' := hadd2 x
      map_smul' := fun a y => by simpa using hsmul2 a x y }
  have ψ₀_apply : ∀ x y, ψ₀ x y = h x y := fun _ _ => rfl
  let ψ : V →+ Module.Dual L V := AddMonoidHom.mk' ψ₀ (fun x x' => by
    ext y
    simp [ψ₀_apply, hadd1])
  have ψ_apply : ∀ x y, ψ x y = h x y := fun _ _ => rfl
  have ψ_smul : ∀ (a : L) x, ψ (a • x) = s a • ψ x := by
    intro a x
    ext y
    simp [ψ_apply, hsmul1]
  have ψ_inj : ∀ x, ψ x = 0 → x = 0 := by
    intro x hx
    exact hnd x (fun y => by rw [← ψ_apply, hx]; rfl)
  have ψ_inj' : ∀ x x', ψ x = ψ x' → x = x' := by
    intro x x' hxx
    exact sub_eq_zero.mp (ψ_inj _ (by rw [map_sub, hxx, sub_self]))

  let b := Module.finBasis L V
  have hli : LinearIndependent L (fun i => ψ (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ψ (∑ j, s (c j) • b j) = 0 := by

      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ψ_smul, hss]
    have h1 := ψ_inj _ h0
    have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
    have h3 := congrArg s h2
    rwa [hss, map_zero] at h3
  have hspan : Submodule.span L (Set.range fun i => ψ (b i)) = ⊤ := by
    refine hli.span_eq_top_of_card_eq_finrank' ?_
    rw [Subspace.dual_finrank_eq]
    simp
  have ψ_surj : ∀ f : Module.Dual L V, ∃ z, ψ z = f := by
    intro f
    have hf : f ∈ Submodule.span L (Set.range fun i => ψ (b i)) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hf
    refine ⟨∑ j, s (c j) • b j, ?_⟩

    rw [map_sum, ← hc]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ψ_smul, hss]
  choose z hz using fun y => ψ_surj ((ψ y).comp g)
  have hz' : ∀ y x, h (z y) x = h y (g x) := by
    intro y x
    rw [← ψ_apply, hz]
    rfl
  refine ⟨{ toFun := z, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro y y'
    apply ψ_inj'
    rw [hz, map_add (f := _), map_add (f := _), hz, hz]
    rfl
  · intro a y
    apply ψ_inj'
    rw [hz, RingHom.id_apply, ψ_smul, ψ_smul, hz]
    rfl
  · intro x y
    show h (g x) y = h x (z y)
    rw [hsymm (z y) x, hz', ← hsymm]

end GlobalTheory.CompanionTheory.Iwahori
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

section Concrete

variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}

theorem hLin_apply (hh : IsHerm s h) (x y : V) : hLin hh x y = h x y := rfl

theorem h_sub_right (hh : IsHerm s h) (x y z : V) : h x (y - z) = h x y - h x z :=
  map_sub (hLin hh x) y z

theorem h_zero_right (hh : IsHerm s h) (x : V) : h x 0 = 0 := map_zero (hLin hh x)

theorem eq_of_pair (hh : IsHerm s h) {z z' : V} (H : ∀ x, h x z = h x z') : z = z' := by
  have : z - z' = 0 := by
    apply hh.2.2.2
    intro y
    rw [hh.2.2.1 y (z - z'), h_sub_right hh, H, sub_self, map_zero]
  exact sub_eq_zero.1 this

theorem s_ne (hδ : δ ≠ 0) : s δ ≠ 0 := by
  simpa using (map_ne_zero s).2 hδ

theorem projE_apply (hh : IsHerm s h) (i : Fin l) (x : V) :
    projE hh δ e f i x = ((s δ)⁻¹ * h (f i) x) • e i := by
  simp [projE, hLin_apply, mul_smul]

theorem projF_apply (hh : IsHerm s h) (i : Fin l) (x : V) :
    projF hh δ e f i x = (δ⁻¹ * h (e i) x) • f i := by
  simp [projF, hLin_apply, mul_smul]

theorem h_f_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if j = i then s δ else 0 := by
  rw [hh.2.2.1 (e j) (f i), hF.2.2.1 j i]
  split_ifs <;> simp

theorem projE_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (e j) = if j = i then e i else 0 := by
  rw [projE_apply, h_f_e hh hF]
  split_ifs
  · simp [s_ne hδ]
  · simp

theorem projE_f (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (f j) = 0 := by
  rw [projE_apply, hF.2.1]; simp

theorem projE_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Fin l) {w : V} (hw : w ∈ W) :
    projE hh δ e f i w = 0 := by
  rw [projE_apply, (hF.2.2.2.1 w hw i).2]; simp

theorem projF_e (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (e j) = 0 := by
  rw [projF_apply, hF.1]; simp

theorem projF_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projF hh δ e f i (f j) = if j = i then f i else 0 := by
  rw [projF_apply, hF.2.2.1 i j]
  by_cases hij : j = i
  · subst hij; simp [hδ]
  · simp [hij, Ne.symm hij]

theorem projF_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Fin l) {w : V} (hw : w ∈ W) :
    projF hh δ e f i w = 0 := by
  rw [projF_apply, (hF.2.2.2.1 w hw i).1]; simp

theorem piece_e (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (e j) = if i = some (Sum.inl j) then e j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_e hh hδ hF, projF_e hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projE_e hh hδ hF]
    · simp [piece, projE_e hh hδ hF, hij, Ne.symm hij]
  · simp [piece, projF_e hh hF]

theorem piece_f (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (f j) = if i = some (Sum.inr j) then f j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_f hh hF, projF_f hh hδ hF]
  · simp [piece, projE_f hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projF_f hh hδ hF]
    · simp [piece, projF_f hh hδ hF, hij, Ne.symm hij]

theorem piece_w (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Idx l) {w : V} (hw : w ∈ W) :
    piece hh δ e f i w = if i = none then w else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_w hh hF _ hw, projF_w hh hF _ hw]
  · simp [piece, projE_w hh hF _ hw]
  · simp [piece, projF_w hh hF _ hw]

theorem end_ext (hF : IsFrame h δ e f W) {A B : Module.End L V} (he : ∀ i, A (e i) = B (e i))
    (hf : ∀ i, A (f i) = B (f i)) (hw : ∀ w ∈ W, A w = B w) : A = B := by
  ext x
  obtain ⟨a, b, w, hwW, rfl⟩ := hF.2.2.2.2.2 x

  simp [map_add (f := _), map_sum, he, hf, hw w hwW]

theorem isPieces_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) :
    IsPieces (piece hh δ e f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_w hh hF _ hw]
  · intro i
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw]
      split_ifs with h1 <;> simp_all [piece_w hh hF _ hw]
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp [LinearMap.sum_apply, piece_e hh hδ hF]
    · simp [LinearMap.sum_apply, piece_f hh hδ hF]
    · simp [LinearMap.sum_apply, piece_w hh hF _ hw]

theorem lat_smul {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {c : L} (hc : ‖c‖ ≤ 1) {x : V} (hx : x ∈ Λ) :
    c • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hx i)

theorem e_mem {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    e j ∈ Λ := by
  have := (hA (Pi.single j 1) 0 0 W.zero_mem).2 ⟨fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], fun i => by simp, by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this

theorem f_mem {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    f j ∈ Λ := by
  have := (hA 0 (Pi.single j 1) 0 W.zero_mem).2 ⟨fun i => by simp, fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this

theorem piece_mem {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (hA : IsAdapted h e f W (fun _ => 1) Λ)
    (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) {x : V} (hx : x ∈ Λ) :
    piece hh δ e f i x ∈ Λ := by
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  obtain ⟨ha, hb, hww⟩ := (hA a b w hw).1 hx
  rcases i with _ | i | i
  · have : piece hh δ e f none (∑ i, a i • e i + ∑ i, b i • f i + w) = w := by

      simp [map_add (f := _), map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    have := (hA 0 0 w hw).2 ⟨fun i => by simp, fun i => by simp, hww⟩
    simpa using this
  · have : piece hh δ e f (some (Sum.inl i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = a i • e i := by

      simp [map_add (f := _), map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using ha i) (e_mem hA hh i)
  · have : piece hh δ e f (some (Sum.inr i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = b i • f i := by

      simp [map_add (f := _), map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using hb i) (f_mem hA hh i)

theorem tor_piece (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) {u : Fin l → L}
    {t : V ≃ₗ[L] V} (ht : IsTor s e f W u t) (i : Idx l) :
    (t.toLinearMap : Module.End L V) * piece hh δ e f i = tau s u i • piece hh δ e f i ∧
      piece hh δ e f i * (t.toLinearMap : Module.End L V) = tau s u i • piece hh δ e f i := by
  obtain ⟨t1, t2, t3⟩ := ht
  constructor
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_e hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t1]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_f hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t2]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_w hh hF _ hw, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t3 w hw]
      · simp
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t1, map_smul,
        piece_e hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t2, map_smul,
        piece_f hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t3 w hw,
        piece_w hh hF _ hw]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp

theorem wt_le {l : ℕ} (i : Idx l) : wt i ≤ 2 * l := by
  rcases i with _ | i | i <;> simp only [wt] <;> omega

theorem wt_injective {l : ℕ} : Function.Injective (wt : Idx l → ℕ) := by
  rintro (_ | i | i) (_ | j | j) hij <;> simp only [wt] at hij <;>
    first
    | rfl
    | (exfalso; have := i.2; omega)
    | (exfalso; have := j.2; omega)
    | (exfalso; have := i.2; have := j.2; omega)
    | (congr 2; apply Fin.ext; have := i.2; have := j.2; omega)

theorem wt_rev {l : ℕ} (i : Idx l) : wt (rev i) + wt i = 2 * l := by
  rcases i with _ | i | i
  · simp only [wt, rev]; omega
  · simp only [wt, rev]; have := i.2; omega
  · simp only [wt, rev]; have := i.2; omega

theorem rev_rev {l : ℕ} (i : Idx l) : rev (rev i) = i := by
  rcases i with _ | i | i <;> rfl

theorem tau_mono (hs : IsInv s) {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (hm : Monotone fun i => ‖u i‖)
    (h1 : ∀ i, ‖u i‖ ≤ 1) (i j : Idx l) (hij : wt i ≤ wt j) : ‖tau s u i‖ ≤ ‖tau s u j‖ := by
  have hinv : ∀ m, 1 ≤ ‖(s (u m))⁻¹‖ := fun m => by
    rw [norm_inv, hs.2.1]
    exact (one_le_inv₀ (norm_pos_iff.2 (hu0 m))).2 (h1 m)
  rcases i with _ | i | i <;> rcases j with _ | j | j <;> simp only [wt] at hij <;> simp only [tau]
  · simp
  · have := j.2; omega
  · simpa using hinv j
  · simpa using h1 i
  · have hij' : i ≤ j := by rw [Fin.le_def]; exact hij
    exact hm hij'
  · exact (h1 i).trans (hinv j)
  · have := i.2; omega
  · have := i.2; have := j.2; omega
  · rw [norm_inv, norm_inv, hs.2.1, hs.2.1]
    refine inv_anti₀ (norm_pos_iff.2 (hu0 j)) (hm ?_)
    have := i.2; have := j.2
    rw [Fin.le_def]; omega

theorem tau_ne {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (i : Idx l) : tau s u i ≠ 0 := by
  rcases i with _ | i | i
  · simp [tau]
  · simpa [tau] using hu0 i
  · simpa [tau] using hu0 i

theorem h_smul_left (hh : IsHerm s h) (c : L) (x y : V) : h (c • x) y = s c * h x y := by
  rw [hh.2.2.1 y (c • x), hh.2.1, map_mul, ← hh.2.2.1 y x]

theorem h_add_left (hh : IsHerm s h) (x x' y : V) : h (x + x') y = h x y + h x' y := by
  rw [hh.2.2.1 y (x + x'), hh.1, map_add (f := _), ← hh.2.2.1 y x, ← hh.2.2.1 y x']

theorem h_zero_left (hh : IsHerm s h) (y : V) : h 0 y = 0 := by
  rw [hh.2.2.1 y 0, h_zero_right hh, map_zero]

theorem h_sum_left (hh : IsHerm s h) {ι : Type} (A : Finset ι) (v : ι → V) (y : V) :
    h (∑ m ∈ A, v m) y = ∑ m ∈ A, h (v m) y :=
  map_sum (⟨⟨fun x => h x y, h_zero_left hh y⟩, fun x x' => h_add_left hh x x' y⟩ : V →+ L) v A

theorem h_sub_left (hh : IsHerm s h) (x x' y : V) : h (x - x') y = h x y - h x' y := by
  rw [hh.2.2.1 y (x - x'), h_sub_right hh, map_sub, ← hh.2.2.1 y x, ← hh.2.2.1 y x']

theorem projE_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projE hh δ e f i x) y = h x (projF hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, hs.1, ← hh.2.2.1 (f i) x]
  ring

theorem projF_adj (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projF hh δ e f i x) y = h x (projE hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, ← hh.2.2.1 (e i) x]
  ring

theorem piece_adj (hs : IsInv s) (hh : IsHerm s h) (i : Idx l) (x y : V) :
    h (piece hh δ e f i x) y = h x (piece hh δ e f (rev i) y) := by
  rcases i with _ | i | i
  · have hx := map_sum (hLin hh x) (fun m => projE hh δ e f m y + projF hh δ e f m y) Finset.univ
    simp only [hLin_apply] at hx
    simp only [piece, rev, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      LinearMap.add_apply, h_sub_left hh, h_sub_right hh, h_sum_left hh, hx, h_add_left hh, hh.1,
      projE_adj hs hh, projF_adj hs hh]
    congr 1
    exact Finset.sum_congr rfl fun m _ => add_comm _ _
  · exact projE_adj hs hh i x y
  · exact projF_adj hs hh i x y

theorem exists_star (hs : IsInv s) (hh : IsHerm s h)
    (hadj : ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y)) :
    ∃ st : Module.End L V → Module.End L V, (∀ g x y, h (g x) y = h x (st g y)) ∧
      (∀ a b, st (a * b) = st b * st a) ∧ st 1 = 1 ∧ st 0 = 0 ∧
      ∀ i : Idx l, st (piece hh δ e f i) = piece hh δ e f (rev i) := by
  choose st hst using hadj
  refine ⟨st, hst, fun a b => ?_, ?_, ?_, fun i => ?_⟩
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, Module.End.mul_apply, Module.End.mul_apply, ← hst, ← hst]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; rfl
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; simp [h_zero_left hh, h_zero_right hh]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, piece_adj hs hh]

end Concrete

end GlobalTheory.CompanionTheory.Iwahori

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.Gauss

open GlobalTheory.CompanionTheory.Iwahori

variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}

theorem eq_zero_of_mul_pieces (hP : IsPieces P) {y : E} (h : ∀ j, y * P j = 0) : y = 0 := by
  have : y * ∑ j, P j = 0 := by
    rw [Finset.mul_sum]; exact Finset.sum_eq_zero (fun j _ => h j)
  rwa [hP.sum, mul_one] at this

theorem eq_zero_of_pieces_mul (hP : IsPieces P) {y : E} (h : ∀ j, P j * y = 0) : y = 0 := by
  have : (∑ j, P j) * y = 0 := by
    rw [Finset.sum_mul]; exact Finset.sum_eq_zero (fun j _ => h j)
  rwa [hP.sum, one_mul] at this

theorem block_mul (hP : IsPieces P) (u x y v : E) :
    u * (x * y) * v = ∑ l, (u * x * P l) * (P l * y * v) := by
  have h : ∀ l, (u * x * P l) * (P l * y * v) = u * x * (P l) * y * v := by
    intro l
    calc (u * x * P l) * (P l * y * v) = u * x * (P l * P l) * y * v := by
          simp only [mul_assoc]
      _ = _ := by rw [hP.idem]
  simp_rw [h]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, hP.sum]
  simp only [mul_one, mul_assoc]

theorem isUpper_mul (hP : IsPieces P) {a b : E} (ha : IsUpper wt P a) (hb : IsUpper wt P b) :
    IsUpper wt P (a * b) := by
  intro i j hij
  rw [block_mul hP]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge (wt l) (wt i) with h | h
  · rw [ha i l h, zero_mul]
  · rw [hb l j (lt_of_lt_of_le hij h), mul_zero]

theorem isLowerUni_mul (hwt : Function.Injective wt) (hP : IsPieces P) {a b : E}
    (ha : IsLowerUni wt P a) (hb : IsLowerUni wt P b) : IsLowerUni wt P (a * b) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [block_mul hP]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge (wt i) (wt l) with h | h
    · rw [ha.1 i l h, zero_mul]
    · rw [hb.1 l j (lt_of_le_of_lt h hij), mul_zero]
  · rw [block_mul hP, Finset.sum_eq_single i]
    · rw [ha.2, hb.2, hP.idem]
    · intro l _ hl
      rcases lt_trichotomy (wt i) (wt l) with h | h | h
      · rw [ha.1 i l h, zero_mul]
      · exact absurd (hwt h).symm hl
      · rw [hb.1 l i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem isUpper_one (hP : IsPieces P) : IsUpper wt P 1 := fun i j h => by
  rw [mul_one]
  exact hP.orth i j (fun e => by subst e; exact lt_irrefl _ h)

theorem isLowerUni_one (hP : IsPieces P) : IsLowerUni wt P 1 := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [mul_one]
    exact hP.orth i j (fun e => by subst e; exact lt_irrefl _ h)
  · rw [mul_one, hP.idem]

theorem sub_one_mul_mem {J : AddSubgroup E} (hJ : IsCongIdeal J P) {a b : E}
    (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) : a * b - 1 ∈ J := by
  have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  rw [this]
  exact J.add_mem (J.add_mem (hJ.mul_mem _ ha _ hb) ha) hb

theorem step (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ)
    (ih : ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b)
    (q : ι) (hq : wt q = m) (x : E) (hx : x ∈ J)
    (hH : ∀ i j, (m + 1 ≤ wt i ∨ m + 1 ≤ wt j) → P i * x * P j = 0) :
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ 1 + x = a * b := by
  have hl : ∀ i, m + 1 ≤ wt i → P i * x = 0 := fun i hi =>
    eq_zero_of_mul_pieces hP fun j => hH i j (Or.inl hi)
  have hr : ∀ j, m + 1 ≤ wt j → x * P j = 0 := fun j hj =>
    eq_zero_of_pieces_mul hP fun i => by rw [← mul_assoc]; exact hH i j (Or.inr hj)
  have hne : ∀ j, m + 1 ≤ wt j → P q * P j = 0 := fun j hj =>
    hP.orth q j (fun e => by subst e; omega)
  have hne' : ∀ j, m + 1 ≤ wt j → P j * P q = 0 := fun j hj =>
    hP.orth j q (fun e => by subst e; omega)
  have hQQ := hP.idem q
  obtain ⟨y, hy, h1, h2⟩ := hJ.inv (x * P q) (hJ.right_mem q x hx)
  obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ J, 1 + z = (1 + y) * (1 + x) :=
    ⟨(1 + y) * (1 + x) - 1,
      sub_one_mul_mem hJ (by rwa [add_sub_cancel_left]) (by rwa [add_sub_cancel_left]),
      by abel⟩
  have hAB : 1 + x = (1 + x * P q) * (1 + z) := by
    rw [hzdef, ← mul_assoc, h1, one_mul]
  have hzQ : z * P q = 0 := by
    have e : (1 + x) * P q = (1 + x * P q) * P q := by
      simp only [add_mul, one_mul, mul_assoc, hQQ]
    have : (1 + z) * P q = P q := by
      calc (1 + z) * P q = (1 + y) * ((1 + x) * P q) := by rw [hzdef, mul_assoc]
        _ = (1 + y) * ((1 + x * P q) * P q) := by rw [e]
        _ = ((1 + y) * (1 + x * P q)) * P q := by rw [mul_assoc]
        _ = P q := by rw [h2, one_mul]
    rw [add_mul, one_mul] at this
    simpa using this
  have hzr : ∀ j, m + 1 ≤ wt j → z * P j = 0 := by
    intro j hj
    have e1 : (1 + x) * P j = P j := by rw [add_mul, one_mul, hr j hj, add_zero]
    have e2 : (1 + x * P q) * P j = P j := by
      rw [add_mul, one_mul, mul_assoc, hne j hj, mul_zero, add_zero]
    have e3 : (1 + y) * P j = P j := by
      calc (1 + y) * P j = (1 + y) * ((1 + x * P q) * P j) := by rw [e2]
        _ = ((1 + y) * (1 + x * P q)) * P j := by rw [mul_assoc]
        _ = P j := by rw [h2, one_mul]
    have : (1 + z) * P j = P j := by
      rw [hzdef, mul_assoc, e1, e3]
    rw [add_mul, one_mul] at this
    simpa using this
  have hzl : ∀ i, m + 1 ≤ wt i → P i * z = 0 := by
    intro i hi
    have e1 : P i * (1 + x) = P i := by rw [mul_add, mul_one, hl i hi, add_zero]
    have e2 : P i * (1 + x * P q) = P i := by
      rw [mul_add, mul_one, ← mul_assoc, hl i hi, zero_mul, add_zero]
    have e3 : P i * (1 + y) = P i := by
      calc P i * (1 + y) = (P i * (1 + x * P q)) * (1 + y) := by rw [e2]
        _ = P i * ((1 + x * P q) * (1 + y)) := by rw [mul_assoc]
        _ = P i := by rw [h1, mul_one]
    have : P i * (1 + z) = P i := by
      rw [hzdef, ← mul_assoc, e3, e1]
    rw [mul_add, mul_one] at this
    simpa using this
  have hsJ : z - P q * z ∈ J := J.sub_mem hz (hJ.left_mem q z hz)
  have hsr : ∀ j, m ≤ wt j → (z - P q * z) * P j = 0 := by
    intro j hj
    rcases hj.eq_or_lt with h | h
    · have : j = q := hwt (h.symm.trans hq.symm)
      subst this
      rw [sub_mul, hzQ, mul_assoc, hzQ, mul_zero, sub_zero]
    · rw [sub_mul, hzr j h, mul_assoc, hzr j h, mul_zero, sub_zero]
  have hsl : ∀ i, m ≤ wt i → P i * (z - P q * z) = 0 := by
    intro i hi
    rcases hi.eq_or_lt with h | h
    · have : i = q := hwt (h.symm.trans hq.symm)
      subst this
      rw [mul_sub, ← mul_assoc, hQQ, sub_self]
    · rw [mul_sub, hzl i h, ← mul_assoc, hne' i h, zero_mul, sub_zero]
  have hS : ∀ i j, (m ≤ wt i ∨ m ≤ wt j) →
      P i * ((1 + (z - P q * z)) - 1) * P j = 0 := by
    intro i j hij
    rw [add_sub_cancel_left]
    rcases hij with h | h
    · rw [hsl i h, zero_mul]
    · rw [mul_assoc, hsr j h, mul_zero]
  obtain ⟨a', b', ha, hb, hau, hbl, hk⟩ :=
    ih (1 + (z - P q * z)) (by rwa [add_sub_cancel_left]) hS
  have hSC : (1 + (z - P q * z)) * (1 + P q * z) = 1 + z := by
    have : (1 + (z - P q * z)) * (1 + P q * z)
        = 1 + z + (z * P q) * z - P q * (z * P q) * z := by noncomm_ring
    rw [this, hzQ]
    simp
  have hA : IsUpper wt P (1 + x * P q) := by
    intro i j hij
    have hm : P i * (1 + x * P q) * P j = P i * P j + P i * x * (P q * P j) := by
      simp only [mul_add, add_mul, mul_one, mul_assoc]
    rw [hm, hP.orth i j (fun e => by subst e; exact lt_irrefl _ hij), zero_add]
    by_cases hjq : j = q
    · subst hjq
      rw [hl i (by omega), zero_mul]
    · rw [hP.orth q j (Ne.symm hjq), mul_zero]
  have hC : IsLowerUni wt P (1 + P q * z) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hm : P i * (1 + P q * z) * P j = P i * P j + (P i * P q) * (z * P j) := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
      rw [hm, hP.orth i j (fun e => by subst e; exact lt_irrefl _ hij), zero_add]
      by_cases hiq : i = q
      · subst hiq
        rw [hzr j (by omega), mul_zero]
      · rw [hP.orth i q hiq, zero_mul]
    · have hm : P i * (1 + P q * z) * P i = P i * P i + (P i * P q) * (z * P i) := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
      rw [hm, hP.idem]
      by_cases hiq : i = q
      · subst hiq
        rw [hzQ, mul_zero, add_zero]
      · rw [hP.orth i q hiq, zero_mul, add_zero]
  refine ⟨(1 + x * P q) * a', b' * (1 + P q * z), ?_, ?_, isUpper_mul hP hA hau,
    isLowerUni_mul hwt hP hbl hC, ?_⟩
  · exact sub_one_mul_mem hJ (by rw [add_sub_cancel_left]; exact hJ.right_mem q x hx) ha
  · exact sub_one_mul_mem hJ hb (by rw [add_sub_cancel_left]; exact hJ.left_mem q z hz)
  · rw [hAB, ← hSC, hk]
    simp only [mul_assoc]

theorem exists_of_support (hwt : Function.Injective wt) (hP : IsPieces P) {J : AddSubgroup E}
    (hJ : IsCongIdeal J P) (m : ℕ) :
    ∀ k : E, k - 1 ∈ J →
      (∀ i j, (m ≤ wt i ∨ m ≤ wt j) → P i * (k - 1) * P j = 0) →
      ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ IsUpper wt P a ∧ IsLowerUni wt P b ∧ k = a * b := by
  induction m with
  | zero =>
    intro k _ h
    have h0 : k - 1 = 0 := eq_zero_of_mul_pieces hP fun j => eq_zero_of_pieces_mul hP fun i => by
      rw [← mul_assoc]; exact h i j (Or.inl (Nat.zero_le _))
    have hk : k = 1 := sub_eq_zero.mp h0
    exact ⟨1, 1, by simp, by simp, isUpper_one hP, isLowerUni_one hP, by simp [hk]⟩
  | succ m ih =>
    intro k hk h
    by_cases hq : ∃ q, wt q = m
    · obtain ⟨q, hq⟩ := hq
      have := step hwt hP hJ m ih q hq (k - 1) hk h
      simpa using this
    · have hq' : ∀ i, m ≤ wt i → m + 1 ≤ wt i := fun i hi => by
        rcases hi.eq_or_lt with e | e
        · exact absurd ⟨i, e.symm⟩ hq
        · exact e
      refine ih k hk fun i j hij => h i j ?_
      rcases hij with e | e
      · exact Or.inl (hq' i e)
      · exact Or.inr (hq' j e)

theorem block_gauss : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ), Function.Injective wt →
    ∀ (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E,
    GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → ∀ k : E, k - 1 ∈ J →
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a ∧
      GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b ∧ k = a * b := by
  intro E ι _ _ wt hwt P hP J hJ k hk
  refine exists_of_support hwt hP hJ (Finset.univ.sup wt + 1) k hk ?_
  intro i j h
  have h1 := Finset.le_sup (f := wt) (Finset.mem_univ i)
  have h2 := Finset.le_sup (f := wt) (Finset.mem_univ j)
  omega

end GlobalTheory.CompanionTheory.Iwahori.Gauss
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.Iwahori.TorusConj

theorem conj_sub_one_mem {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    {P : ι → E} (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) {J : AddSubgroup E}
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J)
    {S S' : E} {σ ρ : ι → L} (hS : ∀ i, P i * S = σ i • P i)
    (hS' : ∀ j, S' * P j = ρ j • P j) (hSS : S * S' = 1) {a : E} (ha : a - 1 ∈ J)
    (h : ∀ i j, ‖σ i * ρ j‖ ≤ 1 ∨ (i ≠ j ∧ P i * a * P j = 0)) :
    S * a * S' - 1 ∈ J := by
  have e1 : S * a * S' - 1 = ∑ i, ∑ j, P i * (S * (a - 1) * S') * P j := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [hP.sum]
    simp [mul_sub, sub_mul, hSS]
  rw [e1]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  have e2 : P i * (S * (a - 1) * S') * P j = (σ i * ρ j) • (P i * (a - 1) * P j) := by
    calc P i * (S * (a - 1) * S') * P j = (P i * S) * (a - 1) * (S' * P j) := by
          simp only [mul_assoc]
      _ = (σ i * ρ j) • (P i * (a - 1) * P j) := by
          rw [hS, hS']
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
          rw [mul_comm]
  rw [e2]
  rcases h i j with hn | ⟨hij, hz⟩
  · exact hc _ hn _ (hJ.right_mem j _ (hJ.left_mem i _ ha))
  · have : P i * (a - 1) * P j = 0 := by
      rw [mul_sub, sub_mul, hz, mul_one, hP.orth i j hij, sub_zero]
    rw [this, smul_zero]
    exact J.zero_mem

theorem conj_congruence {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι]
    (wt : ι → ℕ) (P : ι → E) (hP : GlobalTheory.CompanionTheory.Iwahori.IsPieces P) (J : AddSubgroup E)
    (hJ : GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P)
    (hc : ∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) (T T' : E) (τ : ι → L)
    (hτ : ∀ i, τ i ≠ 0) (hTT : T * T' = 1) (hTT' : T' * T = 1)
    (hl : ∀ i, T * P i = τ i • P i) (hr : ∀ i, P i * T = τ i • P i)
    (hw : ∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) (a b : E) (ha : a - 1 ∈ J) (hb : b - 1 ∈ J)
    (hU : GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a) (hL : GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b) :
    T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  have hl' : ∀ j, T' * P j = (τ j)⁻¹ • P j := by
    intro j
    have e : T' * (T * P j) = T' * (τ j • P j) := by rw [hl]
    rw [← mul_assoc, hTT', one_mul, mul_smul_comm] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  have hr' : ∀ j, P j * T' = (τ j)⁻¹ • P j := by
    intro j
    have e : (P j * T) * T' = (τ j • P j) * T' := by rw [hr]
    rw [mul_assoc, hTT, mul_one, smul_mul_assoc] at e
    rw [eq_inv_smul_iff₀ (hτ j)]
    exact e.symm
  constructor
  · refine conj_sub_one_mem hP hJ hc hr hl' hTT ha fun i j => ?_
    by_cases hij : wt j < wt i
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hU i j hij⟩
    · left
      have hn := hw i j (not_lt.mp hij)
      have hpos : 0 < ‖τ j‖ := norm_pos_iff.mpr (hτ j)
      rw [norm_mul, norm_inv, ← div_eq_mul_inv]
      exact (div_le_one hpos).mpr hn
  · refine conj_sub_one_mem hP hJ hc hr' hl hTT' hb fun i j => ?_
    by_cases hij : wt i < wt j
    · exact Or.inr ⟨fun e => by subst e; exact lt_irrefl _ hij, hL i j hij⟩
    · left
      have hn := hw j i (not_lt.mp hij)
      have hpos : 0 < ‖τ i‖ := norm_pos_iff.mpr (hτ i)
      rw [norm_mul, norm_inv, inv_mul_eq_div]
      exact (div_le_one hpos).mpr hn

end GlobalTheory.CompanionTheory.Iwahori.TorusConj
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Basic\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori.UpInv

variable {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [Fintype ι]

def low (wt : ι → ℕ) (P : ι → Module.End L V) (m : ℕ) : Submodule L V where
  carrier := {x | ∀ i, m ≤ wt i → P i x = 0}
  add_mem' {x y} hx hy i hi := by rw [map_add (f := _), hx i hi, hy i hi, add_zero]
  zero_mem' i _ := map_zero _
  smul_mem' c x hx i hi := by rw [map_smul, hx i hi, smul_zero]

theorem sum_pieces {P : ι → Module.End L V} (hP : IsPieces P) (x : V) :
    ∑ j, P j x = x := by
  have h := congrArg (fun T : Module.End L V => T x) hP.sum
  simpa [LinearMap.sum_apply] using h

theorem map_low_le {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P)
    {a : Module.End L V} (ha : IsUpper wt P a) (m : ℕ) :
    (low wt P m).map a ≤ low wt P m := by
  rintro _ ⟨x, hx, rfl⟩ i hi
  have hx' : x ∈ low wt P m := hx

  rw [← sum_pieces hP x, map_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : m ≤ wt j
  · rw [hx' j hj, map_zero, map_zero]
  · have h := congrArg (fun T : Module.End L V => T x) (ha i j (by omega))
    simpa using h

theorem map_low_eq [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) (m : ℕ) : (low wt P m).map a = low wt P m := by
  let e : V ≃ₗ[L] V := LinearEquiv.ofLinear a a' h1 h2
  exact Submodule.eq_of_le_of_finrank_eq (map_low_le hP ha m)
    (LinearEquiv.finrank_map_eq e (low wt P m))

theorem inv_mem_low [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) {m : ℕ} {x : V} (hx : x ∈ low wt P m) : a' x ∈ low wt P m := by
  rw [← map_low_eq hP h1 h2 ha m] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h := congrArg (fun T : Module.End L V => T y) h2
  have h' : a' (a y) = y := by simpa using h
  rwa [h']

theorem piece_mem_low {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P) (j : ι) (x : V) :
    P j x ∈ low wt P (wt j + 1) := by
  intro i hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  have h := congrArg (fun T : Module.End L V => T x) (hP.orth i j hij)
  simpa using h

theorem isUpper_inv : ∀ {L V ι : Type} [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Fintype ι] (wt : ι → ℕ) (P : ι → Module.End L V),
    GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ a a' : Module.End L V, a * a' = 1 → a' * a = 1 →
      GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a' := by
  intro L V ι _ _ _ _ _ wt P hP a a' h1 h2 ha i j hij
  refine LinearMap.ext fun x => ?_
  have h := inv_mem_low hP h1 h2 ha (piece_mem_low (wt := wt) hP j x) i (by omega)
  simpa using h

end GlobalTheory.CompanionTheory.Iwahori.UpInv

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper =====

-- ===== clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement =====
-- clump-header: {"m": "CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement", "h": "module\n\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsCongIdealTwoTorsion\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntiInvolutionSwapsUpperLower\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceEndomorphismInverseExists\npublic import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HermitianAdjointExists\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsPiecesPiece\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriUpperLowerFactorization\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorusConjugationPreservesCongruence\npublic import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UpperTriangularInverseIsUpper\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.Iwahori

theorem isCongIdeal_congJ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    {π : L} (hπ : ‖π‖ < 1) {ι : Type} (P : ι → Module.End L V)
    (hP : ∀ i, ∀ x ∈ Λ, P i x ∈ Λ) : IsCongIdeal (congJ Λ π) P := by
  refine ⟨?_, ?_, ?_, _root_.GlobalTheory.CompanionTheory.Iwahori.CongUnit.main Λ hΛ π hπ⟩
  · intro x hx y hy v hv
    obtain ⟨z, hz, e1⟩ := hy v hv
    obtain ⟨w, hw, e2⟩ := hx z hz
    refine ⟨π • w, lat_smul hΛ hπ.le hw, ?_⟩
    simp [e1, e2]
  · intro i x hx v hv
    obtain ⟨z, hz, e1⟩ := hx v hv
    exact ⟨P i z, hP i z hz, by simp [e1]⟩
  · intro i x hx v hv
    exact hx _ (hP i v hv)

theorem congJ_smul {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
    {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (π : L) (c : L) (hc : ‖c‖ ≤ 1) (x : Module.End L V)
    (hx : x ∈ congJ Λ π) : c • x ∈ congJ Λ π := by
  intro v hv
  obtain ⟨z, hz, e1⟩ := hx v hv
  refine ⟨c • z, lat_smul hΛ hc hz, ?_⟩
  simp [e1, smul_comm c π z]

theorem isUpper_rev_iff {E : Type} [Ring E] {l : ℕ} (P : Idx l → E) (b : E) :
    IsUpper (fun i => 2 * l - wt i) P b ↔ IsLower wt P b := by
  constructor
  · intro H i j hij
    exact H i j (by have := wt_le i; have := wt_le j; simp only; omega)
  · intro H i j hij
    refine H i j ?_
    have := wt_le i; have := wt_le j
    simp only at hij
    omega

theorem stIwahori : StIwahori := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l e f W Λ hF hΛ hA π hπ k hk hc
  have hδ0 : δ ≠ 0 := hδ.1
  set P := piece hh δ e f with hPdef
  have hP : IsPieces P := isPieces_piece hh hδ0 hF
  have hJ : IsCongIdeal (congJ Λ π) P :=
    isCongIdeal_congJ hΛ hπ P fun i x hx => piece_mem hΛ hA hh hδ0 hF i hx
  obtain ⟨st, hst, st_mul, st_one, st_zero, st_P⟩ :=
    exists_star (δ := δ) (e := e) (f := f) (l := l) hs hh (_root_.GlobalTheory.CompanionTheory.Iwahori.exists_adjoint_herm s hs h hh)
  have hk1 : (k.toLinearMap : Module.End L V) - 1 ∈ congJ Λ π := fun x hx => by
    obtain ⟨y, hy, e1⟩ := hc x hx
    exact ⟨y, hy, by simpa using e1⟩
  obtain ⟨a, b, ha, hb, hup, hlo, hab⟩ := _root_.GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss wt wt_injective P hP _ hJ _ hk1

  obtain ⟨ya, hya, ia1, ia2⟩ := hJ.inv _ ha
  obtain ⟨yb, hyb, ib1, ib2⟩ := hJ.inv _ hb
  rw [add_sub_cancel] at ia1 ia2 ib1 ib2
  have hkk : ∀ y, st (k.toLinearMap) (k y) = y := fun y => by
    refine eq_of_pair hh fun x => ?_
    have := hst k.toLinearMap x (k y)
    simp only [LinearEquiv.coe_coe] at this
    rw [← this, hk x y]
  have hk2 : st (k.toLinearMap) * (k.toLinearMap) = 1 := by
    ext y; exact hkk y
  have hk3 : (k.toLinearMap : Module.End L V) * st (k.toLinearMap) = 1 := by
    ext y
    obtain ⟨z, rfl⟩ := k.surjective y
    simp [hkk z]
  rw [hab] at hk2 hk3
  obtain ⟨ua, ub⟩ := _root_.GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor wt P hP rev rev_rev
    (fun i j hij => by have := wt_rev i; have := wt_rev j; omega) wt_injective st st_mul st_one st_zero st_P
    (fun a a' h1 h2 h3 => _root_.GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv wt P hP a a' h1 h2 h3)
    (fun a a' h1 h2 h3 => (isUpper_rev_iff P a').1 (_root_.GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv _ P hP a a' h1 h2 ((isUpper_rev_iff P a).2 h3)))
    a (1 + ya) b (1 + yb) ia1 ia2 ib1 ib2 hup hlo hk2 hk3
  let A : V ≃ₗ[L] V := LinearEquiv.ofLinear a (1 + ya) ia1 ia2
  let B : V ≃ₗ[L] V := LinearEquiv.ofLinear b (1 + yb) ib1 ib2
  have isoOf : ∀ (g : V ≃ₗ[L] V), st (g.toLinearMap) * g.toLinearMap = 1 → IsIso h g := fun g hg x y => by
    have := hst g.toLinearMap x (g y)
    simp only [LinearEquiv.coe_coe] at this
    rw [this]
    have h2 : st g.toLinearMap (g y) = y := by
      have := congrArg (fun m : Module.End L V => m y) hg
      simpa [Module.End.mul_apply] using this
    rw [h2]
  refine ⟨A, B, isoOf A ua, isoOf B ub, ?_, ?_⟩
  · ext x
    have := congrArg (fun m : Module.End L V => m x) hab
    simpa [A, B, Module.End.mul_apply] using this
  · intro u t hu0 hm h1 ht
    have hT := fun i => tor_piece (δ := δ) hh hδ0 hF ht i
    have key := _root_.GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence wt P hP _ hJ (congJ_smul hΛ π) (t.toLinearMap) (t.symm.toLinearMap) (tau s u)
      (tau_ne hu0) (by ext y; simp [Module.End.mul_apply]) (by ext y; simp [Module.End.mul_apply])
      (fun i => (hT i).1) (fun i => (hT i).2)
      (tau_mono hs hu0 hm h1) a b ha hb hup hlo.1
    constructor
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.1 x hx
      exact ⟨y, hy, by simpa [A, Module.End.mul_apply] using e1⟩
    · intro x hx
      obtain ⟨y, hy, e1⟩ := key.2 x hx
      exact ⟨y, hy, by simpa [B, Module.End.mul_apply] using e1⟩

end GlobalTheory.CompanionTheory.Iwahori

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement =====
