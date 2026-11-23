module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPsEffPullReducedClosedOfDimLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPseudoEffectiveReducedUnivOfSectionPowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeOfIsClosedNeUnivIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_nef_of_hasNonzeroSec_pow_step : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ A M : LB X, IsAmpleLB A → IsNef k M → (∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r)) → IsAmpleLB (tens A M) := by
  intro k _ _ d hd X _ _ hp hX A M hA hM hsec
  obtain ⟨r, hr, hs⟩ := hsec
  refine IsAmpleLB.tens_of_forall_isPsEff k X (strHom k X) hp A M hA hM.isLB ?_
  intro Z hZ
  by_cases hZX : (Z : Set X) = Set.univ
  · exact GlobalTheory.T.isPseudoEffective_reducedUniv_of_section_pow k X hp M hM.isLB r hr hs Z hZX
  · exact GlobalTheory.T.isPsEff_pull_reduced_closed_of_dim_le k d hd X hp M hM Z hZ (GlobalTheory.T.topologicalKrullDim_le_of_isClosed_ne_univ_integral X d hX (Z : Set X) Z.isClosed hZX)

end GlobalTheory
