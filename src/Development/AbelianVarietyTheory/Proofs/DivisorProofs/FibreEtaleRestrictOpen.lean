module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem fibre_etale_restrict_open : ∀ (T X Z T' X' Z' S : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p) (p' : X' ⟶ T') (q' : Z' ⟶ T') (h' : X' ⟶ Z') (hh' : h' ≫ q' = p') (iT : T' ⟶ T) (iX : X' ⟶ X) (iZ : Z' ⟶ Z) [IsOpenImmersion iT] [IsOpenImmersion iX] [IsOpenImmersion iZ] (sZ : iZ ≫ q = q' ≫ iT) (sh : iX ≫ h = h' ≫ iZ) (x : S ⟶ T) (x' : S ⟶ T') (sx : x' ≫ iT = x) (W : (pullback p x).Opens) (w : ↥(pullback p x)) (hw : w ∈ W) (hz : pullback.fst p x w ∈ Set.range iX), Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ (W' : (pullback p' x').Opens) (w' : ↥(pullback p' x')), w' ∈ W' ∧ iX (pullback.fst p' x' w') = pullback.fst p x w ∧ Etale (W'.ι ≫ pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp)) := by
  intro T X Z T' X' Z' S p q h hh p' q' h' hh' iT iX iZ _ _ _ sZ sh x x' sx W w hw hz hE
  have hp : p' ≫ iT = iX ≫ p := by
    simp only [← hh, ← hh', Category.assoc, ← sZ]
    simp only [← Category.assoc, sh]
  have hs : x' ≫ iT = 𝟙 S ≫ x := by simp [sx]
  let j := pullback.map p' x' p x iX (𝟙 S) iT hp hs
  let jZ := pullback.map q' x' q x iZ (𝟙 S) iT sZ.symm hs
  obtain ⟨a', ha'⟩ := hz
  have hwr : w ∈ Set.range j := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨a', ha'⟩, ⟨pullback.snd p x w, by simp⟩⟩
  obtain ⟨w', rfl⟩ := hwr
  set F := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp) with hF
  set F' := pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp) with hF'
  have hnat : j ≫ F = F' ≫ jZ := by
    apply pullback.hom_ext
    · simp only [j, jZ, F, F', Category.assoc]
      rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.assoc, sh]
    · simp only [j, jZ, F, F', Category.assoc]
      rw [pullback.lift_snd, pullback.lift_snd]
      simp only [Category.comp_id]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨j ⁻¹ᵁ W, w', hw, ?_, ?_⟩
  · have e1 : j ≫ pullback.fst p x = pullback.fst p' x' ≫ iX := pullback.lift_fst _ _ _
    have e2 := congrArg (fun f : pullback p' x' ⟶ X => f w') e1
    simp only [Scheme.Hom.comp_apply] at e2
    exact e2.symm
  · have e : ((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ = (j ∣_ W) ≫ (W.ι ≫ F) := by
      rw [Category.assoc, ← hnat, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have : Etale (((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ) := by
      rw [e]; infer_instance
    exact Etale.of_comp _ jZ

end GlobalTheory
