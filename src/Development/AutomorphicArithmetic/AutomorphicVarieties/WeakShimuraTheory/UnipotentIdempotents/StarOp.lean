module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (χ : Fin n → F.G₀ →* Rˣ) (π : Equiv.Perm (Fin n)), (∀ i g, χ i (F.conj g) * χ (π i) g * F.eps O R g ^ ((n : ℤ) - 1) = 1) → F.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
  intro l _ F O _ _ R _ _ n χ π hχ B _ _ _ _ y
  let Ψ : Fin n → MonoidAlgebra B F.G₀ →ₐ[B] B := fun i =>
    MonoidAlgebra.lift B B F.G₀ ((Units.coeHom B).comp (W.pushCh (algebraMap R B) (χ i)))
  have hrep : ∀ z, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => Ψ i z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), ha, hb, Matrix.diagonal_add]
      congr 1
      funext i
      rw [map_add (f := _)]
    | single g b =>
      simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, Ψ]
      ext i j
      simp [W.diagRep, W.pushCh, Matrix.diagonal_apply]
  have hst : ∀ i z, Ψ i (F.star O B n z) = Ψ (π i) z := by
    intro i z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp [W.GFrame.star]
    | add a b ha hb =>
      simp only [W.GFrame.star, map_add (f := _), MulOpposite.unop_add] at ha hb ⊢
      rw [ha, hb]
    | single g b =>
      simp only [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, Ψ]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, map_smul,
        MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, W.pushCh, Units.coe_map,
        smul_eq_mul]
      congr 1
      have he : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
        ext
        simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O R B]
      have key : F.eps O R g ^ (1 - (n : ℤ)) * χ i (F.conj g)⁻¹ = χ (π i) g := by
        have h := hχ i g
        have hb : χ (π i) g = ((χ i) (F.conj g) * F.eps O R g ^ ((n : ℤ) - 1))⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, mul_left_comm, ← mul_assoc]
          exact h
        rw [hb, mul_inv, show (1 : ℤ) - n = -((n : ℤ) - 1) by ring, zpow_neg, map_inv, mul_comm]
      rw [he, ← map_zpow, Units.coe_map, ← key, Units.val_mul]
      simp
  show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (F.star O B n y)) =
    Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
  rw [hrep, hrep, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [hst]
  exact Equiv.prod_comp π (fun i => Ψ i y)
