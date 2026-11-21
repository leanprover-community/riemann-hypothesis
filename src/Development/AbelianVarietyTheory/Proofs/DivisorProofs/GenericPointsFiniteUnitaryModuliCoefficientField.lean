import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.XScov

theorem genericPoints_XF_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), (genericPoints (Xo.XF c)).Finite := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨N, i, hi, hq, he⟩ := Xo.qproj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (KA l) N
  haveI : QuasiCompact Xo.s := he ▸ inferInstance
  haveI : LocallyOfFiniteType Xo.s := he ▸ inferInstance
  haveI : QuasiCompact (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : LocallyOfFiniteType (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : IsLocallyNoetherian (Xo.XF c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : CompactSpace (Xo.XF c) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : IsNoetherian (Xo.XF c) := {}
  exact genericPoints.finite finite_irreducibleComponents_of_isNoetherian

end GlobalTheory.XScov
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoints_finite_unitaryModuli_coefficientField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), (genericPoints (Xo.XF c)).Finite := by
  atlas_forward_decl GlobalTheory.XScov.genericPoints_XF_finite
