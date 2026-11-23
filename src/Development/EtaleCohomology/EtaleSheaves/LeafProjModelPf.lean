module

public import Development.EtaleCohomology.EtaleSheaves.LeafCloseBCut
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace LateralTheory.E.LeafProjModelPf

theorem image_isReduced {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] : IsReduced f.image := by
  have hB := Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing
  have hred : ∀ U : Y.affineOpens, _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U) := fun U =>
    isReduced_of_injective _ (f.toImage_app_injective U)
  refine @isReduced_of_isReduced_stalk _ (fun z => ⟨?_⟩)
  rintro g ⟨n, e⟩
  obtain ⟨U, hzU, s, rfl⟩ := f.image.presheaf.exists_germ_eq g
  rw [← map_pow, ← map_zero (f.image.presheaf.germ _ z hzU).hom] at e
  obtain ⟨V, hzV, iU, iV, e'⟩ := f.image.presheaf.germ_eq z hzU hzU _ 0 e
  rw [map_pow, map_zero] at e'
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, hWV⟩ := Opens.isBasis_iff_nbhd.mp hB hzV
  have h0 : f.image.presheaf.map (homOfLE hWV).op (f.image.presheaf.map iU.op s) = 0 := by
    have hx := congrArg (f.image.presheaf.map (homOfLE hWV).op) e'
    rw [map_pow, map_zero] at hx
    exact (hred ⟨W, hW⟩).eq_zero _ ⟨n, hx⟩
  rw [← f.image.presheaf.germ_res iU z hzV, ← f.image.presheaf.germ_res (homOfLE hWV) z hzW]
  simp only [CommRingCat.comp_apply] at h0 ⊢
  rw [h0, map_zero]

theorem image_irreducible {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [IrreducibleSpace X] :
    IrreducibleSpace f.image := by
  have h1 : IsIrreducible (Set.range f.toImage) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
  have h2 := h1.closure
  rw [f.toImage.denseRange.closure_range] at h2
  exact (irreducibleSpace_def _).mpr h2

theorem leafImageIntegral {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] (hX : IsIntegral X) :
    IsIntegral f.image := by
  have := image_isReduced f
  have := image_irreducible f
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def LeafQProjImm : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (N : ℕ) (φ : Spec (CommRingCat.of A) ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace k N),
    IsImmersion φ ∧ QuasiCompact φ ∧
    φ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str k N = Spec.map (CommRingCat.ofHom (algebraMap k A))

theorem LeafProjModel_of (h1 : LeafQProjImm) : LateralTheory.E.LeafCloseBCut.LeafProjModel := by
  intro k _ A _ _ _ _
  obtain ⟨N, φ, hi, hq, hc⟩ := h1 k A
  refine ⟨φ.image, φ.imageι ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str k N, φ.toImage, leafImageIntegral φ inferInstance,
    ?_, inferInstance, ?_⟩
  · have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
    infer_instance
  · rw [← Category.assoc, Scheme.Hom.toImage_imageι]; exact hc

end LateralTheory.E.LeafProjModelPf
