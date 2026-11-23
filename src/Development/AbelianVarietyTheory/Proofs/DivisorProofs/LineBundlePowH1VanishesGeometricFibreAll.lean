module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesOfIsoOfIsGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw.SecBC


open GlobalTheory.AbLaw in
theorem GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar
    (hV : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B]
      (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → FirstCohomologyVanishes (pw M (a : ℤ)))
    (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (hA : IsAbelianScheme A)
    (hL : L.IsLB) (hAm : RelAmple A L) (a : ℕ) (ha : 1 ≤ a) (T : Over S) (K : Type) [Field K] [IsAlgClosed K]
    (q : Spec (CommRingCat.of K) ⟶ T.left) :
    ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)),
      IsPullback π f' (fst T A).left q ∧ FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  let s : Spec (CommRingCat.of K) ⟶ S := q ≫ T.hom
  let AK : Over (Spec (CommRingCat.of K)) := (Over.pullback s).obj A
  let g : AK.left ⟶ A.left := pullback.fst A.hom s
  have hg : IsPullback g AK.hom A.hom s := IsPullback.of_hasPullback A.hom s
  let M : LB AK.left := L.pull g
  have hM : M.IsLB := LB.isLB_pull hL g
  have hAK : IsAbelianScheme AK := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := s (default : PrimeSpectrum K)) trivial
  have hsub : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hMA : RelAmple AK M := ReciprocityTheory.ChartRestriction.G.Geo.Tor.relAmple_pull (w := ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso M) hg hL hM
    ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hM)) U hU
    (fun y => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]) hAm
  have hK := hV K AK M hAK hM hMA a ha
  have H := isPullback_snd A T
  let π : AK.left ⟶ (T ⊗ A).left := H.lift g (AK.hom ≫ q) (by rw [hg.w, Category.assoc])
  have e₁ : π ≫ (snd T A).left = g := H.lift_fst _ _ _
  have e₂ : π ≫ (fst T A).left = AK.hom ≫ q := H.lift_snd _ _ _
  refine ⟨AK.left, π, AK.hom, IsPullback.of_right (by rw [e₁]; exact hg) e₂ H, ?_⟩
  refine h1Zero_of_isIso _ _ (𝟙 _) (pw M a) _ inferInstance (isLB_pw hM _)
    (LB.isLB_pull (LB.isLB_linComb hL _ _) π) ?_ hK
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (chartOut L (fun _ : Fin 1 => (snd T A).left) (fun _ => (a : ℤ)) π
    (fun _ => 𝟙 _ ≫ g) fun _ => by rw [e₁, Category.id_comp]) (chartPw M a)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm (ReciprocityTheory.ChartRestriction.G.Geo.Tor.iso_linComb
      ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hM))
      (fun _ : Fin 1 => 𝟙 _) (fun _ => (a : ℤ))))

theorem GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all : ((∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π)) := by
  intro hV S A _ _ L hA hL hAm a ha T K _ _ q
  exact GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar hV S A L hA hL hAm a ha T K q
