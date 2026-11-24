module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.LamSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

theorem UpperTheory.V.Ws.H5.isTwistOf :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) {R : Type} [CommRing R] (x x' : B.B →+* R) (γ : F.G₀ →* Rˣ), TwMap B x x' γ → (B.u.D.map x).IsTwist γ (B.u.D.map x') := by
  intro l _ F O _ _ _ n r B R _ x x' γ h
  have hmap (f : B.B →+* R) : ∀ i g, (B.u.D.map f).lam i (MonoidAlgebra.single g 1) =
      f (B.u.D.lam i (MonoidAlgebra.single g 1)) := by
    have hchi : ∀ y, (B.u.D.map f).chi (MonoidAlgebra.mapRingHom F.G₀ f y) = (B.u.D.chi y).map f := by
      intro y
      have he : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C (MonoidAlgebra.mapRingHom F.G₀ f y) =
          MonoidAlgebra.mapRingHom F.G₀ (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom F.G₀ C y) := by
        rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
          ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
          ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
      show (B.u.D.map f).D R[X] _ = _
      rw [he]
      let : Algebra B.B R[X] := ((algebraMap R R[X]).comp f).toAlgebra
      have hc : ∀ a : B.B, Polynomial.mapRingHom f (algebraMap B.B B.B[X] a) = algebraMap B.B R[X] a := by
        intro a
        change Polynomial.map f (C a) = C (f a)
        exact Polynomial.map_C f
      exact B.u.D.nat B.B[X] R[X] { Polynomial.mapRingHom f with commutes' := hc } _
    have hm : ∀ i y, (B.u.D.map f).lam i (MonoidAlgebra.mapRingHom F.G₀ f y) = f (B.u.D.lam i y) := by
      intro i y
      simp only [GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
    intro i g
    simpa using hm i (MonoidAlgebra.single g 1)
  have e : B.u.D.map x' = twD (B.u.D.map x) γ := by
    refine UpperTheory.V.CA.d_gext _ _ fun g i _ hi => ?_
    have s : MonoidAlgebra.single g ((1 : R) * algebraMap R R (γ g)) =
        (γ g : R) • MonoidAlgebra.single g (1 : R) := by
      simp
    rw [lam_twD, twA_single, s, lamSmul, min_eq_left hi, hmap x, hmap x']
    exact h.1 g i hi
  rw [e]
  exact isTwist_twD _ _
