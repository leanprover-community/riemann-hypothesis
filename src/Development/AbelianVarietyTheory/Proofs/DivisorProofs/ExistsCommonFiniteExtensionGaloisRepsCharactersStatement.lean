module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFiniteExtensionGaloisRepsCharacters
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

theorem _root_.GlobalTheory.T.exists_common_finiteExtension_galoisReps_characters : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n a t : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (ρ : G E Ω →* GL (Fin a) (PadicAlgCl l)) (χ : Fin t → G E Ω →* (PadicAlgCl l)ˣ), Continuous r → Continuous ρ → (∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) → ∃ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧ (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ g i j, (ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ s g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 := by
  first | exact @GlobalTheory.RepFinExtJoint.finext_joint | exact GlobalTheory.RepFinExtJoint.finext_joint | (intros; apply GlobalTheory.RepFinExtJoint.finext_joint <;> assumption)
