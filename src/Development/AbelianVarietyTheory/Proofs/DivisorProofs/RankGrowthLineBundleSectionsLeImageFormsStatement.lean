module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLineBundleSectionsLeImageForms
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

@[expose] public section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem _root_.GlobalTheory.T.rankGrowth_lineBundle_sections_le_image_forms : ∀ (k : Type) [Field k] [CharZero k] (S : LinSys k), S.IsVariety → S.BasePointFree → S.Birational → growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤ growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) := by
  first | exact @GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms | exact GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms | (intros; apply GlobalTheory.SecGrowth.rankGrowth_lineBundleSections_le_image_forms <;> assumption)
