module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTwistCharacterUnitsModSpecialIdeal
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

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_twistCharacter_units_mod_specialIdeal : ∀ (D : D7) (p : ℕ) (I : Ideal (𝓞 D.host.E)) (xi : (AfE D)ˣ →* ℂˣ), p.Prime → p.Coprime (D.host.g 0 * D.host.g 1) → I * I.map (barE D : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {((p : ℕ) : 𝓞 D.host.E)} → I ⊔ I.map (barE D : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ → XiOK D p xi → ∃ χ : (𝓞 D.host.E ⧸ I)ˣ →* (FO D)ˣ, χ ≠ 1 ∧ ∀ (x : (AfE D)ˣ) (a : 𝓞 D.host.E) (u : (𝓞 D.host.E ⧸ I)ˣ), NormOne x → CongOne (D.host.g 0 * D.host.g 1) x → (u : 𝓞 D.host.E ⧸ I) = Ideal.Quotient.mk I a → (x : AfE D) - 1 ⊗ₜ (a : D.host.E) ∈ GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (I : Set (𝓞 D.host.E))) → ((xi x : ℂˣ) : ℂ) = (((χ u : (FO D)ˣ) : FO D) : ℂ) := by
  first | exact @GlobalTheory.TwistChar.exists_char_of_xiOK | exact GlobalTheory.TwistChar.exists_char_of_xiOK | (intros; apply GlobalTheory.TwistChar.exists_char_of_xiOK <;> assumption)
