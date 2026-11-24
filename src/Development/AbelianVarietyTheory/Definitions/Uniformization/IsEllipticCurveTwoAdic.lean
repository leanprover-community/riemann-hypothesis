module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.SettingConsistentExample

theorem exists_even_one {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (P : CP G)
    (i : H ⟶ G) (hi : i = 1) : ∃ σ : CubTriv P.c i, σ.Even := by
  subst hi
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ := (PEmpty.elim : PEmpty → (H.left ⟶ G.left))) (ε := PEmpty.elim)
    (K' := Fin 2) (φ' := ![(1 : H ⟶ G).left, (1 : H ⟶ G).left]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen P.L.L) (LB.isGen_oneGen _)
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ H.left) (z : Z) (J), Good P.L.L z J → val t r z J = 1 :=
    fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨t, ht, fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · simp only [v _ _ z J hJ, MonObj.comp_one, (isCub_cubV P.c hJ).face, _root_.mul_one]
  · show val t _ z J = _ * val t _ z J
    rw [v _ _ z J hJ, v _ _ z J hJ, MonObj.comp_one, P.val_sym_one hJ, _root_.mul_one]

section Generic
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

variable (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (X : Type) [AddCommGroup X] [Subsingleton X]






omit hG' in
theorem ab_even (P : CP G) : ∃ σ : CubTriv P.c (TQ.abelian G hG X).i, σ.Even :=
  exists_even_one _ _ (Hom.one_def).symm

end Generic

section Thick
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]




end Thick

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

end GlobalTheory.UU.SettingConsistentExample
end
