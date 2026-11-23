module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsHyp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvFamNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSubfieldModel
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtConclOfIsoOf
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

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.PTN

theorem ptConclAt_all_of (hfs : PtfsHyp) (hL : LocHyp) :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω],
      PTConclAt F Ω := by
  intro F Ω _ _ _ _ _
  obtain ⟨K, hK, hC, e, E, h⟩ := GlobalTheory.CompanionTheory.FieldModel.exists_subfield_model F Ω
  exact ptConcl_of_iso_of hL F Ω K (AlgebraicClosure ℚ) e E h (hfs K)

theorem poitouTateNormalised_of (hfs : PtfsHyp) (hL : LocHyp) (hvan : VanishAll) :
    PoitouTateNormalised := by
  intro F Ω _ _ _ _ _ l _ r hl hr ζ hζ
  obtain ⟨inv, hinv⟩ := GlobalTheory.CompanionTheory.PoitouTateInv.exists_invFam_normalised F Ω l r hr ζ hζ
  refine ⟨inv, hinv, ?_⟩
  intro S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have h := ptConclAt_all_of hfs hL F Ω l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨h.1, h.2, hvan F Ω l r hl hr S hS M ρ hρ⟩

end PositivityTheory.PTN
