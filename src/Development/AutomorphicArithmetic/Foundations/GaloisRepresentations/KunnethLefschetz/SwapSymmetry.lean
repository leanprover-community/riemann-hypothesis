module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem pb_self (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (n : ℤ) (x : V l X n) : pb l (𝟙 X) n x = x := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem pb_comp_apply (l : ℕ) [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.swap_holds :
    UpperTheory.Gal.KunnethLefschetz.Swap := by
  intro hP l _ k _ _ hl d X p hSP hR G n w h h' x
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  have hpair := (hP k d p inferInstance hsm).1
  have hunit : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hu := hR.mul_one X hunit
  have key : ∀ f : pullback p p ⟶ X, pullback.diagonal p ≫ f = 𝟙 X →
      cupV l (pullback p p) h (pb l f n x) (G.diag d p) = G.g hpair h x := by
    intro f hf
    have hd : G.diag d p = G.g hpair (show (0 : ℤ) + 2 * d = 2 * d by simp) (oneV l X) := by
      simp only [GysQ.diag, GysQ.cls, dif_pos hpair]
    rw [hd, ← G.proj hpair (show n + 0 = n by simp) h (show (0 : ℤ) + 2 * d = 2 * d by simp) h,
      ← pb_comp_apply, hf, pb_self, hu]
  rw [key _ (by simp), hR.comm (pullback p p) (2 * d) n w h' h,
    key _ (by simp), Int.negOnePow_even _ ⟨d * n, by ring⟩, one_smul]
