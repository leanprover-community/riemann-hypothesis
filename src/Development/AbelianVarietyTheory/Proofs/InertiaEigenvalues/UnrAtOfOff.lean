module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistUnrOff

theorem unrAt_of_off : ∀ (D : D7) (δ : GlobalTheory.ExportSeries.Twist D Circle), δ.Good → ∀ (χ : Formalism.L2.Host.HChar D.host.E), ChrEq δ.chi χ → ∀ P : Pl D.host.E, P ∉ δ.Q → (¬ ∃ P' ∈ δ.Q, Formalism.IndefR.Lev.IsConjPl P' P) → χ.UnrAt P := by
  intro D δ hδ χ hc P hPQ hconj
  rw [← GlobalTheory.LFun.unrAt_iff_of_chrEq hc P]
  apply GlobalTheory.GoodModUnr.unrAt_of_unrPl
  intro e f hp x hx h2 h3
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hp
  have hoff := GlobalTheory.ExportSeries.TupleChars.unrOff_of_unram hδ.unram hδ.split (Finset.Subset.refl _)
  refine hoff _ ε hε ?_ x hx h2 h3
  intro PP hPP hu
  rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu.symm with h | h
  · exact hPQ (h ▸ hPP)
  · exact hconj ⟨PP, hPP, (GlobalTheory.IdemSupport.isConjPl_iff PP P).2 h⟩

end GlobalTheory.TwistUnrOff
