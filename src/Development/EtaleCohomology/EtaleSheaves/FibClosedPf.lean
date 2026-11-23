module

public import Development.EtaleCohomology.EtaleSheaves.FibClosed
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf

namespace LateralTheory.E.FibClosedPf

abbrev fm {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    pullback (c ≫ p) (cpt A) ⟶ pullback p (cpt A) :=
  pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp)

def FibQCQS : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A))
  [QuasiCompact c] [QuasiSeparated c], QuasiCompact (fm c p) ∧ QuasiSeparated (fm c p)

def FibStalk : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.map (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s) (𝟙 _)
      ((pullback p (cpt A)).fromSpecStalk s) (fm c p) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem FibClosed_of (hZ : ZLG) (h0 : HZero) (hA : AICAcyc) (hQ : FibQCQS) (hS : FibStalk) : FibClosed := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB
  obtain ⟨_, _⟩ := hQ A c p
  obtain ⟨_, _⟩ := qcqs_of (pullback.snd p (cpt A))
  have hu : IsUnit (q : Γ(pullback p (cpt A), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  exact hZ H q (fm c p) (𝟙 _) hu i (hS H h0 hA q i A hq c p hZs hSs hB)

theorem fm_isPullback {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    IsPullback (fm c p) (pullback.fst (c ≫ p) (cpt A)) (pullback.fst p (cpt A)) c := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p (cpt A)) (h₂₂ := p) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback p (cpt A)).flip
  have e : fm c p ≫ pullback.snd p (cpt A) = pullback.snd (c ≫ p) (cpt A) := by
    unfold fm; rw [pullback.map]; erw [pullback.lift_snd]; simp
  rw [e]
  exact (IsPullback.of_hasPullback (c ≫ p) (cpt A)).flip

theorem fibQCQS : FibQCQS := by
  intro A _ _ Z S c p _ _
  exact ⟨MorphismProperty.of_isPullback (P := @QuasiCompact) (fm_isPullback c p).flip ‹_›,
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (fm_isPullback c p).flip ‹_›⟩

end LateralTheory.E.FibClosedPf
