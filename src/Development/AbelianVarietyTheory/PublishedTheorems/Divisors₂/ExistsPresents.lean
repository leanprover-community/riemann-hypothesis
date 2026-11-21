import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernDegreePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel

namespace GlobalTheory.Published.ChernDegreeComplexModel

variable (Y : Var ℂ)

theorem exists_presents {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) :
    ∃ (Δ : Y.Dv) (r : L.ι → Y.Fnˣ), Presents Δ L r := by
  obtain ⟨i₀, h₀⟩ := exists_chart φ.isLB (genericPoint Y.X)
  exact ⟨ofLB φ.isLB i₀ h₀, frameRat L i₀ h₀, presents_ofLB φ.isLB i₀ h₀⟩


theorem integrable {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) := by
  have : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  let R := AnRead.all Y.str (RingHom.id ℂ) Y.dim
  have hs : φ.IsSmooth R := (Weight.isCInf_iff_isSmooth R).1 h
  have hm := ReciprocityTheory.AnForm.M.mIntegrableCont R.finAtlas (fun _ => φ.locPot)
    (fun _ => Weight.isPotential_locPot hs) (fun _ => 1) continuous_const
  exact ((Weight.chernInt_eq_mInt R h measurable_const).1).2 hm


theorem point (Δ : (proj ℂ 0).Dv) (L : LB (proj ℂ 0).X) (φ : Weight (proj ℂ 0).str (RingHom.id ℂ) L)
    (h : φ.IsCInf) : φ.chernInt 0 Set.univ (fun _ => 1) = ((proj ℂ 0).inter (fun _ => Δ) : ℝ) :=
  (chernDegree_point (RingHom.id ℂ) Δ L φ h).2



end GlobalTheory.Published.ChernDegreeComplexModel
