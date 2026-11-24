module

public import Development.EtaleCohomology.TateTwists.EtaleTensorPreservesQuasiIsoOfAcyclicAndCone
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.acyc

def LocAcyc {R : Type} [CommRing R] (C : Cx R) : Prop :=
  ∀ (U : Scheme.{0}) (n : ℤ) (z : Sec (C.X n) U), Sec.map (C.d n (n + 1)) z = 0 →
    Loc U fun V g => ∃ y : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) y = Sec.res g z

def ColExact {R : Type} [CommRing R] (C J : Cx R) : Prop :=
  ∀ (U : Scheme.{0}) (s t : ℤ) (x : Sec (C.X s) U ⊗[ULift.{1} R] Sec (J.X t) U),
    TensorProduct.map ((C.d s (s + 1)).hom.app (op U)).hom LinearMap.id x = 0 →
    Loc U fun V g => ∃ y : Sec (C.X (s - 1)) V ⊗[ULift.{1} R] Sec (J.X t) V,
      TensorProduct.map ((C.d (s - 1) s).hom.app (op V)).hom LinearMap.id y =
        TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom x

def acycIff : Prop := ∀ (R : Type) [CommRing R] (C : Cx R), C.Acyclic ↔ LocAcyc C

def column : Prop := ∀ (R : Type) [CommRing R] (C J : Cx R), (∀ t, FlatS (J.X t)) → LocAcyc C → ColExact C J

def stair : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → ColExact C J → LocAcyc T

end LateralTheory.EtaleFoundations.acyc

open LateralTheory.EtaleFoundations.acyc in
theorem LateralTheory.EtaleFoundations.tqis.acyc_of (hI : acycIff) (hC : column) (hS : stair) : LateralTheory.EtaleFoundations.tqis.acyc := by
  intro R _ C J T a b _ _ τ hτ hJ hCa
  exact (hI R T).2 (hS R a b τ hτ (hC R C J hJ ((hI R C).1 hCa)))
