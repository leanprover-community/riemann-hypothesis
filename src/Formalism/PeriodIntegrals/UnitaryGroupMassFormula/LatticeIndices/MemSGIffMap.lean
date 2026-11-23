module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CardNuGZmod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlags
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParGMapGlRed
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 MassDataIdxRed
open Formalism.DoubleCosetMeasures (IsUpUni)

variable {A B : Type} [CommRing A] [CommRing B] {r k : ℕ}

theorem mem_sG_iff_map (f : A →+* B) (hf : Function.Injective f) (g : GL (Idx r k) A) :
    g ∈ sG A r k ↔ glRed f g ∈ sG B r k := by
  change Par _ (g : Matrix (Idx r k) (Idx r k) A) ↔ Par _ ((glRed f g : GL (Idx r k) B) : Matrix (Idx r k) (Idx r k) B)
  rw [glRed_coe]
  set x : Matrix (Idx r k) (Idx r k) A := (g : Matrix (Idx r k) (Idx r k) A) with hx
  have z0 : ∀ {a : A}, f a = 0 → a = 0 := fun h => hf (by rw [h, map_zero])
  have z1 : ∀ {a : A}, f a = 1 → a = 1 := fun h => hf (by rw [h, map_one])
  constructor
  · intro h
    refine MassDataIdxStImB.par_map f (map_zero f) (map_one f) (fun h hh => ?_) h
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hh.map f
  · rintro ⟨h11, h33, h21, h31, h32, h, _, h22⟩
    have u11 : IsUpUni (b11 x) :=
      ⟨fun i j hij => z0 (h11.1 hij), fun a => z1 (h11.2 a)⟩
    have u33 : IsUpUni (b33 x) :=
      ⟨fun i j hij => z0 (h33.1 hij), fun a => z1 (h33.2 a)⟩
    have v21 : b21 x = 0 := by ext i j; exact z0 (congrFun (congrFun h21 i) j)
    have v31 : b31 x = 0 := by ext i j; exact z0 (congrFun (congrFun h31 i) j)
    have v32 : b32 x = 0 := by ext i j; exact z0 (congrFun (congrFun h32 i) j)
    have v22 : b22 x = midEmb (Matrix.of fun i j => x (wI i) (wI j)) := by
      ext i j
      have e := congrFun (congrFun h22 i) j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z0 (by simpa [b22, midEmb] using e)
      · exact z1 (by simpa [b22, midEmb] using e)
    refine ⟨u11, u33, v21, v31, v32, Matrix.of fun i j => x (wI i) (wI j), ?_, v22⟩
    show IsUnit (Matrix.det _)
    rw [← det_shape u11 u33 v21 v31 v32 _ v22, hx]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

end MassDataIdxStIm
