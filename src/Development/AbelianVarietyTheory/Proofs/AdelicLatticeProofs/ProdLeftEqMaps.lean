module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Maps
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.ProductLeftMaps

open TensorProduct

theorem prodLeft_eq_maps {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : TensorProduct F (A × B) E) :
    TensorProduct.prodLeft F F A B E z =
      ((Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F A E) z,
       (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F B E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul x e =>
    obtain ⟨a, b⟩ := x
    simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
    rfl

theorem main : ∀ {F A B E : Type} [inst : Field F] [inst_1 : CommRing A] [inst_2 : CommRing B]
    [inst_3 : CommRing E] [inst_4 : Algebra F A] [inst_5 : Algebra F B] [inst_6 : Algebra F E]
    (z : TensorProduct F (A × B) E),
    (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F A E) z = (0 : TensorProduct F A E) →
    (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F B E) z = (0 : TensorProduct F B E) →
    z = (0 : TensorProduct F (A × B) E) := by
  intro F A B E _ _ _ _ _ _ _ z h1 h2
  apply (TensorProduct.prodLeft F F A B E).injective
  rw [prodLeft_eq_maps, h1, h2, map_zero]
  rfl

end GlobalTheory.ProductLeftMaps
