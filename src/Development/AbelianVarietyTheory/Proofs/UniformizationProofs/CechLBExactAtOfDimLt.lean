module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCoversStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCoverOfIsProjByOfInfinite
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbLaw

theorem cechLB_exactAt_of_dim_lt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (Y : Scheme.{0}) [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) (g : ℕ) (M : LB Y), SmoothOfRelativeDimension g f → IsProjBy f → IsSeparated f → M.IsLB → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, g < n → (cechLB f M D).ExactAt n := by
  intro K _ _ Y _ f g M hf hp hs hM κ _ _ D hD hc n hn
  obtain ⟨E, hE, hEc⟩ := GlobalTheory.AffineCover.exists_cover_of_isProjBy K Y f g hf hp
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_cechLB_homology_equiv_of_affine_covers K Y f M κ D (Fin (g + 1)) E hM hs hD hc hE hEc n
  have hz : IsZero ((cechLB f M E).X n) := isZero_cechLB_X f M E (by simpa using hn)
  have hE0 : IsZero ((cechLB f M E).homology n) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((cechLB f M E).homology n) := ModuleCat.isZero_iff_subsingleton.1 hE0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AbLaw
