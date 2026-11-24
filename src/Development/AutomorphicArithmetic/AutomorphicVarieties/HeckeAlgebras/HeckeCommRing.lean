module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open IsLocalRing

namespace UpperTheory.V.Hi

variable {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]

instance heckeCommRing (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] : CommRing (heckeAlg Y op) :=
  { (inferInstance : Ring (heckeAlg Y op)) with
    mul_comm := fun a b => by
      have key : {t : Module.End A Y | ∃ i, Restr t (op i)}.Pairwise Commute := by
        rintro s ⟨i, hi⟩ t ⟨j, hj⟩ _
        change s * t = t * s
        refine LinearMap.ext fun y => Subtype.ext ?_
        change (s (t y) : M) = t (s y)
        rw [hi, hj, hj, hi]
        exact h.out.2 i j y y.2
      exact (Algebra.isMulCommutative_adjoin A key).is_comm.comm a b }

def heckeGen (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] (i : ι) : heckeAlg Y op :=
  ⟨(op i).restrict (h.out.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩

theorem IsCNL.ofCO (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R] [Algebra O R]
    [Alg.IsCO O R] : IsCNL R := by
  exact
    { complete := inferInstance
      finite := Finite.of_surjective (ResidueField.map (algebraMap O R))
        (Alg.resMap_bijective O R).2 }

end UpperTheory.V.Hi
