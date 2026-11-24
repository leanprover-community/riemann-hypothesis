module

public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace AdeleBaseChange

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


variable (K) in
def finiteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


variable (L) in
def finiteRestrict (v : HeightOneSpectrum (𝓞 K)) : 𝔸[L] →+* CompletionsOver L v where
  toFun y w := y.2 w.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

def completionsOverBasis (v : HeightOneSpectrum (𝓞 K)) :
    Basis ι (v.adicCompletion K) (CompletionsOver L v) :=
  (Algebra.TensorProduct.basis (v.adicCompletion K) b).map (tensorEquiv L v).toLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
theorem completionsOverBasis_repr (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v)
    (i : ι) : (completionsOverBasis b v).repr z i = localCoord b v i z :=
  rfl

theorem finiteEval_norm (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    finiteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm (v.adicCompletion K) (finiteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (finiteEval K v) (finiteRestrict L v) (adeleBasis (Module.finBasis K L))
    (completionsOverBasis (Module.finBasis K L) v) (fun y i ↦ ?_) y).symm
  rw [completionsOverBasis_repr, adeleBasis_repr]
  rfl

theorem norm_adeleRing_snd (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) (y.2 w.1) :=
  (finiteEval_norm v y).trans (norm_pi _)


variable (K) in
def infiniteEval (v : InfinitePlace K) : 𝔸[K] →+* v.Completion where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl


variable (L) in
def infiniteRestrict (v : InfinitePlace K) :
    𝔸[L] →+* GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v where
  toFun y w := y.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def piPlacesOverBasis (v : InfinitePlace K) :
    Basis ι v.Completion (GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v) :=
  (Algebra.TensorProduct.basis v.Completion b).map
    (GroundTheory.Global.InfinitePlace.tensorPiEquiv (L := L) v).toLinearEquiv

theorem piPlacesOverBasis_repr (v : InfinitePlace K)
    (z : GroundTheory.Global.InfinitePlace.PiPlacesOver (L := L) v) (i : ι) :
    (piPlacesOverBasis b v).repr z i = GroundTheory.Global.InfinitePlace.piPlacesOverCoord b v i z :=
  rfl

theorem infiniteEval_norm (v : InfinitePlace K) (y : 𝔸[L]) :
    infiniteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm v.Completion (infiniteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (infiniteEval K v) (infiniteRestrict L v)
    (adeleBasis (Module.finBasis K L)) (piPlacesOverBasis (Module.finBasis K L) v)
    (fun y i ↦ ?_) y).symm
  rw [piPlacesOverBasis_repr, adeleBasis_repr]
  rfl


open scoped Classical in
theorem norm_adeleRing_fst (v : InfinitePlace K) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y.1 w) :=
  by
    letI : ∀ w : v.placesOver L, Module.Finite v.Completion (w : InfinitePlace L).Completion :=
      fun w => GroundTheory.Global.InfinitePlace.finiteDimensional_completion v
        (w : InfinitePlace L)
    exact (infiniteEval_norm v y).trans (GroundTheory.Global.Algebra.norm_pi _)

end AdeleBaseChange

open AdeleBaseChange SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem ideleNorm_snd (x : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) ((x : 𝔸[L]).2 w.1) :=
  norm_adeleRing_snd (K := K) v (x : 𝔸[L])


open scoped Classical in
theorem ideleNorm_fst (x : IdeleGroup L) (v : InfinitePlace K) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion ((x : 𝔸[L]).1 w) :=
  norm_adeleRing_fst (K := K) v (x : 𝔸[L])

end

end GroundTheory.Global
