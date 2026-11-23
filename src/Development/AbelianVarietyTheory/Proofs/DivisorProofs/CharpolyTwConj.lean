module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FibStable

section Generic

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun x => ⟨1, by simp⟩, fun ⟨g, h⟩ => ⟨g⁻¹, by rw [h, map_inv]; group⟩,
    fun ⟨g, h⟩ ⟨k, h'⟩ => ⟨g * k, by rw [h', h, map_mul]; group⟩⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

theorem rep_cls (θ : G →* G) (y : G) : ∃ g, (cls θ y).rep = g⁻¹ * y * θ g :=
  (cls_eq_iff θ _ _).1 (cls_rep θ (cls θ y)).symm

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [nrmL_twConj, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

end Local

end GlobalTheory.BCT.FibStable
