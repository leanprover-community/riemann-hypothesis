module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValues
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem _root_.GlobalTheory.T.tame_character_values_eq_heckeChar_local_values : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] (σ : K →+* ℂ) (μ : Chr F E K) (ξ : Formalism.L2.Host.HChar E), GlobalTheory.Mem.Col2.Reads σ μ ξ → (∀ P, ξ.TameAt P) → ∀ P : HeightOneSpectrum (𝓞 E), (ξ.UnrAt P → σ ((unifVal μ P : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ)) ∧ (((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ ((qVal μ P : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TwistVal.main | exact GlobalTheory.TwistVal.main | (intros; apply GlobalTheory.TwistVal.main <;> assumption)
