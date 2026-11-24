module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

theorem isIso_of_isAffine_of_coheight_le_one {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] [IsAffine X] [IsAffine Y] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) : IsIso f := by
  have h : IsIso (f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_of_coheight_le_one f hf ⊤)
  have : IsIso (Spec.map f.appTop) := inferInstance
  have e : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  rw [e]
  infer_instance

theorem eq_of_isAffineOpen_of_ringKrullDim_le_one (X : Scheme.{0}) [IsLocallyNoetherian X]
    [X.IsSeparated] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (V V' : X.Opens)
    (hV : IsAffineOpen V) (hle : V ≤ V')
    (h : ∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) : V' = V := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  refine le_antisymm (fun z hz ↦ ?_) hle
  obtain ⟨_, ⟨N, hN, rfl⟩, hzN, hNV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz V'.isOpen
  have hN' : IsAffineOpen N := hN
  have hNV' : IsAffineOpen (N ⊓ V) := hN'.inf hV
  have : IsAffine N := hN'
  have : IsAffine (N ⊓ V : X.Opens) := hNV'
  have hiso : IsIso (X.homOfLE (inf_le_left : N ⊓ V ≤ N)) := by
    refine isIso_of_isAffine_of_coheight_le_one _ fun x hx ↦ ?_
    have hx' : Order.coheight (Scheme.Opens.ι N x) ≤ 1 := by rwa [coheight_apply_of_isOpenImmersion]
    have hxV : Scheme.Opens.ι N x ∈ V := h _ (hNV x.2) ((ringKrullDim_stalk_le_one_iff _).mpr hx')
    exact ⟨⟨x.1, x.2, hxV⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  obtain ⟨y, hy⟩ := (X.homOfLE (inf_le_left : N ⊓ V ≤ N)).surjective ⟨z, hzN⟩
  have hyz : y.1 = z := (Scheme.homOfLE_apply _ y).symm.trans (congrArg Subtype.val hy)
  exact hyz ▸ y.2.2

end GlobalTheory
