module

public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.WeilBound.ThetaLifts.SphericalLattices.GenOf
public import Development.WeilBound.ThetaLifts.SphericalLattices.LocDataV
public import Development.WeilBound.ThetaLifts.SphericalLattices.LocDataVAlt
public import Development.WeilBound.ThetaLifts.SphericalLattices.UnrAtDiv
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem howeInert : HoweInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he
  obtain ⟨⟨w, hin⟩, hvT⟩ := inert_ctx hT he
  have ha : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.α u :=
    fun u hu => hT.chars.unrα u fun h => hvT (hu ▸ h)
  have hb : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.β u :=
    fun u hu => hT.chars.unrβ u fun h => hvT (hu ▸ h)
  refine ⟨fun ω ρ hL => ?_, fun ω ρ hL => ?_⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hb
      (fun u hu => unrAt_div (hb u hu) (ha u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' ha
      (fun u hu => unrAt_div (ha u hu) (hb u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV' hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩

end PositivityTheory.Sph

end
