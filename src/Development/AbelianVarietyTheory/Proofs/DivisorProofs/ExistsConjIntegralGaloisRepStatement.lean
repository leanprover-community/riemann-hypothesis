module

public import Formalism.ConjugateSelfDual.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIntegralGaloisRep
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

theorem _root_.GlobalTheory.T.exists_conj_integral_galoisRep : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (LL : FinExt l) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)), Continuous r → (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) → ∃ A : GL (Fin n) (PadicAlgCl l), (∀ i j, (A : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ i j, ((A⁻¹ : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ g i j, ‖((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1 := by
  first | exact @GlobalTheory.GalIntegral.exists_conj_integral | exact GlobalTheory.GalIntegral.exists_conj_integral | (intros; apply GlobalTheory.GalIntegral.exists_conj_integral <;> assumption)
