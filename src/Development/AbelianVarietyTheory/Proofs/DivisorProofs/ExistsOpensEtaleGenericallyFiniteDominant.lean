module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GenEtale

theorem exists_opens_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hd
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper π := IsProper.of_comp π p
  have := hp.isLocallyNoetherian
  have := hp.charZero
  obtain ⟨U, -, hU, hxU, hW, -, hE, -⟩ :=
    GlobalTheory.GenFiniteEtale.exists_finite_etale_of_isProper π hη hd ⊤ (Opens.mem_top _)
  refine ⟨π ⁻¹ᵁ U, ⟨genericPoint Y, show π _ ∈ U from hη ▸ hxU⟩, ?_⟩
  have : IsAffine U := hU
  have : IsAffine (π ⁻¹ᵁ U) := hW
  have hE' : ∀ U' : X.Opens, U' = U → (π.app U').hom.Etale := by
    rintro _ rfl
    exact hE
  have e : U.ι ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have h1 : Etale (π ∣_ U) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
    exact (RingHom.Etale.respectsIso).cancel_right_isIso _ _ |>.2 (hE' _ e)
  rw [← morphismRestrict_ι]
  infer_instance

end GlobalTheory.GenEtale
