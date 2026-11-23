module

public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeCharProductFormulaNormOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem _root_.GlobalTheory.T.heckeChar_productFormula_normOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (rep : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E)) (V : Finset (HeightOneSpectrum (𝓞 F))) (x z : Eˣ), (∀ y : F, star (algebraMap F E y) = algebraMap F E y) → Module.finrank F E = 2 → (∃ a : E, star a ≠ a) → (∀ P : HeightOneSpectrum (𝓞 E), ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) → χ.TrivOn F → (∀ P, χ.TameAt P) → (∀ P, conjPrime₂ P = P → χ.UnrAt P) → (∀ v, (rep v).under (𝓞 F) = v) → (x : E) = z * star (x : E) → (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ V → χ.UnrAt P ∧ P.valuation E (x : E) = 1) → χ.inf x * ∏ v ∈ V, χ.locK (rep v) z = 1 := by
  first | exact @GlobalTheory.NormOneProd.inf_mul_prod | exact GlobalTheory.NormOneProd.inf_mul_prod | (intros; apply GlobalTheory.NormOneProd.inf_mul_prod <;> assumption)
