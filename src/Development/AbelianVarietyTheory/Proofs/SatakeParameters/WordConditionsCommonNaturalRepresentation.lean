module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HodgeTateJumpsAtModulesForSign
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThickLetterWordLatticeSurjectionHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgeTateJumpsCoefficientExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneLeScOfSizeData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsAtPlaceOfFrobeniusOrbitStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem lowCount_eq_smallHodgeTateJumpCountOverLetter {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} (W : Wach P K LL)
    [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : Lat K LL) (a : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (η : ℕ) :
    TruncatedSeriesCountingBounds.lowCount W T a η = lowCount W T a η := by
  unfold TruncatedSeriesCountingBounds.lowCount lowCount
  congr 1

theorem recS_wordBase_natural : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∃ (ε : ℤˣ) (g : ZMod (RecS.nLet i w hw) → D.R.GG), IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ RecS.WordBase L HW i r ρ π w hw Cx hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i r ρ π w hw Cx hG hR h7 hF hJ hP h2 hq hd
  obtain ⟨ε, κ, hin⟩ := GlobalTheory.T.hodgeTateJumps_coefExt_of_roomy_adm7 L C₀ i r ρ π w hw Cx hR h7 hF hJ hP
  let C : Enl D i w hw := ⟨Cx.LL, Cx.inc⟩
  obtain ⟨g, hg, hwb⟩ := GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit L C₀ HW i w hw C hG r ρ π ε κ hR h7 h2 hq hd hin
  refine ⟨ε, g, hg, ?_⟩
  have hsm := GlobalTheory.HTW.Rec.recWord_small_pos L C₀ (liftIdx D i) ε g _ hR hg
  obtain ⟨hdeg, hloc, hnum⟩ := hwb
  refine
    { unram := hloc.unram
      deg := hdeg
      split := hloc.split
      t1 := fun T h => ?_
      t2 := fun T h => ?_
      t2win := fun T h => ?_
      num := hnum
      small := hsm }
  · obtain ⟨h1, h2, h3⟩ := hloc.t1 T h
    exact ⟨h1, h2, h3⟩
  · obtain ⟨⟨h1, _, _⟩, h4⟩ := hloc.t2 T h
    refine ⟨h1, fun ft a => ?_⟩
    rw [lowCount_eq_smallHodgeTateJumpCountOverLetter]
    exact h4 ft a
  · obtain ⟨⟨_, h2, h3⟩, _⟩ := hloc.t2 T h
    exact ⟨h2, h3⟩

end GlobalTheory.HTW.Rec
