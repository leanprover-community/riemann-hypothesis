module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumAxes

theorem one_comp_hom' {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem gen_pull_lam {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (c : T ⟶ G2 G) (hc : c ≫ fst G G = 1 ∨ c ≫ snd G G = 1) :
    ∃ t : ((abelian₂ G L).pull c.left).Gen, t.IsGen := by
  have hR : GlobalTheory.CoordToExt.Refines ((abelian₂ G L).pull c.left) L
      (fun p : PUnit × ULift.{0} (Finset (Fin 2)) => c.left ≫ (psum G (x2 G) p.2.down).left)
      (fun p => (-1) ^ (2 - p.2.down.card) * 1) :=
    (GlobalTheory.CoordToExt.refines_self (L := L) _ _).linComb _ _
  refine hR.exists_gen hL (φ' := PEmpty.elim) (ε' := PEmpty.elim) ?_ (LB.oneGen L) GlobalTheory.CoordToExt.isGen_one
  intro U _ h
  have hp : ∀ I : Finset (Fin 2), c.left ≫ (psum G (x2 G) I).left = (psum G ![c ≫ fst G G, c ≫ snd G G] I).left :=
    fun I => by
      have := psum_hom (preHom (G := G) c) (x2 G) I
      have e : (fun i => preHom (G := G) c (x2 G i)) = ![c ≫ fst G G, c ≫ snd G G] := by
        funext i; fin_cases i <;> rfl
      rw [e] at this
      exact congrArg (fun z => z.left) this
  simp only [hp]
  rw [Fintype.prod_prod_type]
  have hu : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  simp only [Finset.univ_unique, Finset.prod_singleton, hu]
  simp only [Finset.prod_insert (by decide : (⟨∅⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{0}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{1}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0, 1}⟩} : Finset _)),
    Finset.prod_singleton]
  have p0 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs ∅ = 1 := fun _ => rfl
  have p1 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0} = xs 0 * 1 := fun _ => rfl
  have p2 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {1} = xs 1 * 1 := fun _ => rfl
  have p3 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0, 1} = xs 0 * (xs 1 * 1) := fun _ => rfl
  simp only [p0, p1, p2, p3, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, Finset.univ_eq_empty,
    Finset.prod_empty]
  rcases hc with hc | hc <;> simp [hc]

theorem gen_axes : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (L : LB G'.left), L.IsLB → ∀ (u v : G ⟶ G'), IsMonHom u → IsMonHom v → ∀ P : LB (G2 G).left, P.IsLB →
    LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ u) (snd G G ≫ v)).left) →
    (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧
      (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) := by
  intro S G G' _ _ _ _ L hL u v hu hv P hP hiso
  have hΛ : (abelian₂ G' L).IsLB := GlobalTheory.SabBaseChange.cube_isLB (x2 G') hL
  have key : ∀ a : G ⟶ G2 G, (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)) ≫ fst G' G' = 1 ∨
      (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)) ≫ snd G' G' = 1 → ∃ t : (P.pull a.left).Gen, t.IsGen := by
    intro a ha
    have h1 : LBIso (P.pull a.left) ((abelian₂ G' L).pull (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)).left) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hiso a.left (Over.comp_left ..)
    obtain ⟨t, ht⟩ := gen_pull_lam hL _ ha
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hΛ _) (pull_isLB hP _) h1.symm t ht
  refine ⟨key _ (Or.inl ?_), key _ (Or.inr ?_)⟩
  · rw [Category.assoc, lift_fst, lift_fst_assoc]; exact one_comp_hom' u
  · rw [Category.assoc, lift_snd, lift_snd_assoc]; exact one_comp_hom' v

end GlobalTheory.MumAxes
