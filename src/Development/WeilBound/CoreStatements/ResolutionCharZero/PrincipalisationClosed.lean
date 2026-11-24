module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PrincipalisationOfCharZero
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.PrincipalizationOfPrincipalisation
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroOfBoundary
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem principalisation_closed : GlobalTheory.Published.Principalisation := by
  intro k _ _ d Y f hY hd hp I hI
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth d f
  have hP : IsProper f := isProper_of_isProjOver hp
  obtain ⟨X', s, E', hseq, hsm', hcart, hsnc, hiso⟩ :=
    principalisationCharZero_bot_closed k d Y f hd inferInstance inferInstance I (not_subset_of_ne_bot hI)
  obtain ⟨y, hy⟩ := GlobalTheory.Principalise.nonempty_compl_support hI
  have hne : Nonempty X' := by
    obtain ⟨w, hw⟩ := (s ∣_ I.support.compl).homeomorph.surjective ⟨y, hy⟩
    exact ⟨(s ⁻¹ᵁ I.support.compl).ι w⟩
  have hint : IsIntegral X' := isIntegral_of_seq hseq hY hne hsm'
  have hproj : IsProjOver (s ≫ f) :=
    (Resolution.IsBlowupSeq.of_smooth hseq.isSmoothBlowupSeq).isProjOver hp
  have hdense : Dense ((s ⁻¹ᵁ I.support.compl : X'.Opens) : Set X') := by
    have := dense_compl_of_snc _ hsnc
    rw [Scheme.IdealSheafData.support_comap] at this
    exact this.mono fun x hx => hx
  have hrel : SmoothOfRelativeDimension d (s ≫ f) :=
    relDim_of_dense _ _ hdense (relDim_preimage s f _ (by
      have : SmoothOfRelativeDimension (0 + d) (Scheme.Opens.ι I.support.compl ≫ f) := inferInstance
      simpa using this))
  have hc := seq_of_iso hseq hY hp hne I.support.compl hiso
  refine ⟨X', s, hint, hrel, hproj, hc.mono ?_, hiso, hcart, hsnc⟩
  intro x hx
  simpa using hx

end PositivityTheory.ResPlug.WeightsCompactStabilizer
