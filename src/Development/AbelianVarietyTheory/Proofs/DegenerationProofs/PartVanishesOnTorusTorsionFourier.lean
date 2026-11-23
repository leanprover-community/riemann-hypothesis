module

import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MeetsOpensOfSeparatesSections
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointTranslatePure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinsuppEqZeroOfSumTorsionCharactersEqZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorsionFourier

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X} {U : X.Opens}

theorem valF_sum (h : ⊤ ≤ x ⁻¹ᵁ U) {J : Type} (A : Finset J) (a : J → Γ(X, U)) :
    valF x U (∑ j ∈ A, a j) = ∑ j ∈ A, valF x U (a j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [valF, dif_pos h, map_sum]

theorem valF_ne_zero_iff_le (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  apply GlobalTheory.MatchCoord.valF_ne_zero_iff <;> assumption

theorem le_nonzeroLocus_iff {H : LB X} (s : H.Sec) (x : Sp F ⟶ X) :
    ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s ↔ ∃ l, ⊤ ≤ x ⁻¹ᵁ H.U l ∧ valF x (H.U l) (s.f l) ≠ 0 := by
  constructor
  · intro h
    have hp : x (IsLocalRing.closedPoint F) ∈ Out.nonzeroLocus s :=
      h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have h1 : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (s.f l) := by
      intro y _
      have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
      subst this
      exact hl
    have h2 : ⊤ ≤ x ⁻¹ᵁ H.U l := h1.trans (Scheme.Hom.preimage_mono x (X.basicOpen_le _))
    exact ⟨l, h2, (valF_ne_zero_iff_le h2 _).2 h1⟩
  · rintro ⟨l, h2, hne⟩
    exact ((valF_ne_zero_iff_le h2 _).1 hne).trans
      (Scheme.Hom.preimage_mono x (le_iSup (fun k => X.basicOpen (s.f k)) l))

end Val

theorem part_vanishes_on_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (d n : ℕ), (n : k) ≠ 0 → ∀ φ : (Φ.H d).Sec, (∀ α ∈ Φ.supp φ, ∀ β ∈ Φ.supp φ, (∃ w, α = β + n • w) → α = β) → (∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) → ∀ α ψ, Φ.IsPart α φ ψ → ∀ x : Φ.Pt, x ^ n = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus ψ) := by
  intro k _ _ Φ d n hn φ hinc hφ α ψ hψ x hx hle
  classical
  obtain ⟨hex, hfin, hext, hsum⟩ := GlobalTheory.ZH.WtPart.weight_parts k Φ d
  obtain ⟨l, hl, hne⟩ := (le_nonzeroLocus_iff (F := k) ψ x.left).1 hle
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := ⟨hn0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n

  have hα : α ∈ Φ.supp φ := by
    by_contra hα
    apply hne
    have h0 : ψ.f l = ∑ β ∈ (∅ : Finset Φ.E.X), ((fun _ => ψ) β).f l := by
      refine hsum ψ ∅ (fun _ => ψ) ?_ (fun β hβ => absurd hβ (Finset.notMem_empty β)) l
      rintro β ⟨l', hl'⟩
      have e : β = α := hψ.1 ⟨l', hl'⟩
      subst e
      exact absurd ⟨l', by rwa [← hψ.2 l']⟩ hα
    refine (congrArg (valF (F := k) x.left _) h0).trans ((valF_sum (F := k) hl _ _).trans ?_)
    exact Finset.sum_empty
  choose p hp using hex φ
  let p' : Φ.E.X → (Φ.H d).Sec := fun β => if β = α then ψ else p β
  have hp' : ∀ β, Φ.IsPart β φ (p' β) := fun β => by
    by_cases h : β = α
    · subst h
      simpa only [p', if_pos rfl] using hψ
    · simpa only [p', if_neg h] using hp β
  let A : Finset Φ.E.X := (hfin φ).toFinset
  have hA : ∀ β, β ∈ A ↔ β ∈ Φ.supp φ := fun β => (hfin φ).mem_toFinset
  let v : Φ.E.X → k := fun β => valF (F := k) x.left ((Φ.H d).U l) ((p' β).f l)
  let c : Φ.E.X →₀ k := Finsupp.indicator A fun β _ => v β
  have hcs : c.support ⊆ A := Finsupp.support_indicator_subset _ _
  have hc : c = 0 := by
    refine GlobalTheory.finsupp_eq_zero_of_sum_torsion_characters_eq_zero k Φ.E.X n ζ (Nat.pos_of_ne_zero hn0) hζ k c
      (fun a ha b hb => hinc a ((hA a).1 (hcs ha)) b ((hA b).1 (hcs hb))) fun t ht => ?_
    obtain ⟨a, -, ha, hat⟩ := GlobalTheory.TorusTranslate.exists_point_translate_pure k Φ t
    have hax : (a * x) ^ n = 1 := by
      rw [mul_pow, ha n ht, hx, _root_.one_mul]
    have hl' := (hat d α ψ hψ.1 x l hl).1
    have h0 : valF (F := k) (a * x).left ((Φ.H d).U l) (φ.f l) = 0 := by
      by_contra h
      exact hφ _ hax ((le_nonzeroLocus_iff (F := k) φ (a * x).left).2 ⟨l, hl', h⟩)
    rw [Finsupp.sum_of_support_subset c hcs _ (fun _ _ => smul_zero _), ← h0]
    have h1 := hsum φ A p' (fun β hβ => (hA β).2 hβ) (fun β _ => hp' β) l
    refine Eq.trans ?_ ((congrArg (valF (F := k) (a * x).left _) h1).trans (valF_sum (F := k) hl' _ _)).symm
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [Finsupp.indicator_of_mem hβ]
    exact (hat d β (p' β) (hp' β).1 x l hl).2.symm
  have h2 : c α = v α := Finsupp.indicator_of_mem ((hA α).2 hα) _
  apply hne
  have h3 : v α = 0 := by rw [← h2, hc]; rfl
  have h4 : p' α = ψ := if_pos rfl
  rw [← h4]
  exact h3

end GlobalTheory.TorsionFourier
