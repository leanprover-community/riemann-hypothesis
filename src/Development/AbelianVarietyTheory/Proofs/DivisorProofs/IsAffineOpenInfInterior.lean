module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffOff

theorem isAffineOpen_inf_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ U : Y.X.affineOpens, IsAffineOpen (U.1 ⊓ interior Y) := by
  intro E _ _ _ H Dw l Xo c Y h U
  have hs := snc_gen_iff.1 h
  unfold boundary at hs
  set V := interior Y with hVdef
  have key : ∀ y : Y.X, ∃ W : Y.X.Opens, y ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (V.ι ⁻¹ᵁ W) := by
    intro y
    obtain ⟨-, W, hy, n, f, J, -, hI⟩ := hs y
    have e : W.1 ⊓ V = Y.X.basicOpen (∏ i ∈ J, f i) := by
      ext z
      constructor
      · rintro ⟨hW, hV⟩
        by_contra hz
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
          exact hz
        rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
        exact this hV
      · intro hz
        have hW : z ∈ W.1 := Y.X.basicOpen_le _ hz
        refine ⟨hW, by_contra fun hV ↦ ?_⟩
        have : z ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
          rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
          exact hV
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem hW, hI, Scheme.zeroLocus_span,
          Scheme.zeroLocus_singleton] at this
        exact this hz
    refine ⟨W.1, hy, W.2, ?_⟩
    rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm, e]
    exact W.2.basicOpen _
  have : IsAffineHom V.ι := isAffineHom_of_forall_exists_isAffineOpen _ key
  have h2 := U.2.preimage V.ι
  rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at h2
  rwa [inf_comm]

end GlobalTheory.AffOff
