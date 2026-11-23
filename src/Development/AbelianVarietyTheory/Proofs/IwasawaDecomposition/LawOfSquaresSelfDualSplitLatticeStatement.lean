module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawOfSquaresSelfDualSplitLattice
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem _root_.GlobalTheory.T.law_of_squares_selfDual_splitLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n r : ℕ), Odd r → ∀ (L : Submodule (𝓞 E) (Fin n → E)) (cc : Ideal (𝓞 E)), (⟨L⟩ : GenLat E n).Unimod → GenLat.SplitSupp H (⟨L⟩ : GenLat E n) → cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → Submodule.span (𝓞 E) (detSet L) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc → ∃ q : ℚ, 0 < q ∧ q ^ 2 * (((L ⊓ Formalism.L2.Pj.stdLat E n).toAddSubgroup.addSubgroupOf L.toAddSubgroup).index : ℚ) ^ r = (Ideal.absNorm cc : ℚ) := by
  first | exact @GlobalTheory.LawOfSquares.law_of_squares | exact GlobalTheory.LawOfSquares.law_of_squares | (intros; apply GlobalTheory.LawOfSquares.law_of_squares <;> assumption)
