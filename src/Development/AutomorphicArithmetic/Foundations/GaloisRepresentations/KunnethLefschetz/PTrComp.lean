module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pb_id (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) : pb l (𝟙 X) n = LinearMap.id := by
  show pullHQ l (sch.map (𝟙 X)) n 0 = _
  rw [sch.map_id]
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]

private theorem lift_square {A B C : Scheme.{0}} (i : A ⟶ C) [IsOpenImmersion i] (y : B ⟶ C) (y' : B ⟶ A)
    (h : y' ≫ i = y) : IsPullback y' (𝟙 B) i y := (IsPullback.of_horiz_isIso_mono ⟨by simp [h]⟩ : IsPullback (𝟙 B) y' y i).flip

private theorem pt_restrict {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} {p : X ⟶ S k}
    (U : X.Opens) (y : Pt p) (y' : Pt (U.ι ≫ p)) (hy : y'.1 ≫ U.ι = y.1)
    (h : IsPair d 0 p y.1) (h' : IsPair d 0 (U.ι ≫ p) y'.1) :
    pb l U.ι _ (G.pt d y) = G.pt d y' := by
  show pb l U.ι _ (G.cls d 0 p y.1) = G.cls d 0 (U.ι ≫ p) y'.1
  unfold GysQ.cls
  rw [dite_eq_left h, dite_eq_left h', G.nat h' h U.ι (𝟙 _) rfl (lift_square U.ι y.1 y'.1 hy), pb_id]
  rfl

theorem trComp_holds : TrComp := by
  intro hC hO hP l _ k _ _ hl R G d hint X p hsp hpj
  obtain ⟨m, U, hU, hcov, hdisj⟩ := hC k d p hsp hpj
  have hex : ∀ j, ∃ lam : V l (U j : Scheme) (2 * d) →ₗ[ℚ_[l]] ℚ_[l],
      ∀ y : Pt ((U j).ι ≫ p), lam (G.pt d y) = 1 :=
    fun j => hint _ (hU j).1 (hU j).2.1 (hU j).2.2
  choose lamj hlamj using hex
  refine ⟨∑ j, (lamj j).comp (pb l (U j).ι (2 * d)), fun y => ?_⟩
  have hsep : IsSeparated p := by
    haveI := hsp.1
    infer_instance
  obtain ⟨hy, -⟩ := (hP k d p hsep hsp.2).2 y
  obtain ⟨s⟩ : Nonempty (S k) := inferInstance
  have hrange : Set.range y.1 = {y.1 s} := by
    ext t
    constructor
    · rintro ⟨t', rfl⟩
      rw [Subsingleton.elim t' s]
      rfl
    · intro ht
      exact ⟨s, ht.symm⟩
  obtain ⟨j, hj⟩ := hcov (y.1 s)
  have hsub : Set.range y.1 ⊆ Set.range (U j).ι := by
    rw [Scheme.Opens.range_ι, hrange]
    simpa using hj
  let y' : Pt ((U j).ι ≫ p) :=
    ⟨IsOpenImmersion.lift (U j).ι y.1 hsub, by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2⟩
  have hfac : y'.1 ≫ (U j).ι = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hsep' : IsSeparated ((U j).ι ≫ p) := by
    haveI := (hU j).1.1
    infer_instance
  have hy' : IsPair d 0 ((U j).ι ≫ p) y'.1 := ((hP k d ((U j).ι ≫ p) hsep' (hU j).1.2).2 y').1
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [LinearMap.comp_apply, pt_restrict G d (U j) y y' hfac hy hy', hlamj]
  · intro j' _ hj'
    obtain ⟨W, hW⟩ := hO.1 y.1 hy.cl
    have hle : U j' ≤ W := by
      intro t ht
      show t ∈ (W : Set X)
      rw [hW, hrange]
      rintro (rfl : t = y.1 s)
      exact (hdisj j' j hj').le_bot (show y.1 s ∈ U j' ⊓ U j from ⟨ht, hj⟩)
    rw [LinearMap.comp_apply, ← Scheme.homOfLE_ι X hle, pb_comp, LinearMap.comp_apply]
    unfold GysQ.pt GysQ.cls
    rw [dite_eq_left hy, G.off hy _ W hW, map_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

end UpperTheory.Gal.KunnethLefschetz
