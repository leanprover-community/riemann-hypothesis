module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LeOfPowLePolyMulPow
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud GlobalTheory.HTPull GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.tatePull_of :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R]
      (b : GBase D.toG R) (N : ℕ) (S S₁ : Scheme.{0})
      (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (f : S₁ ⟶ S)
      (o : GObj b N s) (o₁ : GObj b N s₁) (m : GObjMap o₁ o f)
      (k : Type) [Field k] (t : Sp k ⟶ S₁) (I : UpperTheory.Gal.Int.Geo.TIso o (t ≫ f)),
      ∃ I₁ : UpperTheory.Gal.Int.Geo.TIso o₁ t, ∀ n y,
        (I₁.ev n y).left ≫ m.φ = (I.ev n y).left := by
  intro p _ D R _ _ b N S S₁ s s₁ f o o₁ m k _ t I
  letI := o.grp
  letI := o₁.grp
  letI := o.comm
  have hl : ∀ x : Over.mk t ⟶ o₁.A,
      Over.Hom.left (pushHom m.cart (Over.mk t) x) = Over.Hom.left x ≫ m.φ := fun _ => rfl
  let E := MulEquiv.ofBijective (pushHom m.cart (Over.mk t))
    ⟨push_injective m.cart _, push_surjective m.cart _⟩
  have key : ∀ q, Over.Hom.left (E.symm q) ≫ m.φ = Over.Hom.left q := fun q => by
    rw [← hl]
    exact congrArg Over.Hom.left (E.apply_symm_apply q)
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n y => E.symm (I.ev n y),
            add := fun n x y => by simp only [I.add, map_mul],
            lin := fun n c x => ?_,
            ker := fun n hn x => by
              rw [← I.ker n hn x]
              exact E.symm.map_eq_one_iff,
            onto := fun n hn q => ?_,
            tower := fun n j hn hj x => by rw [← map_pow, I.tower n j hn hj x],
            isom := fun n hn x y => ?_ }, fun n y => key (I.ev n y)⟩
  · have h1 := push_comp m.cart (m.act c) (Over.mk t) (E.symm (I.ev n x))
    have h2 : pushHom m.cart (Over.mk t) (E.symm (I.ev n x)) = I.ev n x := E.apply_symm_apply _
    rw [h2] at h1
    apply E.injective
    rw [E.apply_symm_apply, I.lin]
    exact h1.symm
  · constructor
    · intro hq
      obtain ⟨x, hx⟩ := (I.onto n hn (E q)).1 (by rw [← map_pow, hq, map_one])
      exact ⟨x, by rw [hx, E.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      rw [← map_pow, (I.onto n hn _).2 ⟨x, rfl⟩, map_one]
  · exact (weilIs_grpPullback_of_comm _ _ _ _ f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o₁.isLB _)
      m.cart (diag_iso m.sq m.pol) (Over.mk t) _ _ _ _ _ _ (key _).symm (key _).symm).2
      (I.isom n hn x y)
