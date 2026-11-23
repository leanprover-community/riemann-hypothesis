module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTest
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SelfDualMap

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

section Coord

variable {F : Type} [Field F] [NumberField F]

def complReal (v : InfinitePlace F) (hv : v.IsReal) : v.Completion ≃ₜ ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toEquiv.toHomeomorphOfIsInducing (by
    have hf : (⇑(InfinitePlace.Completion.ringEquivRealOfIsReal hv).toEquiv) =
        ⇑(InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) :=
      funext fun x => InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv x
    rw [hf]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.isInducing)

theorem complReal_add (v : InfinitePlace F) (hv : v.IsReal) (x y : v.Completion) :
    complReal v hv (x + y) = complReal v hv x + complReal v hv y :=
  map_add (InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y

def ainfReal (hF : ∀ v : InfinitePlace F, v.IsReal) : InfiniteAdeleRing F ≃ₜ (InfinitePlace F → ℝ) :=
  Homeomorph.piCongrRight fun v => complReal v (hF v)

theorem ainfReal_add (hF : ∀ v : InfinitePlace F, v.IsReal) (x y : InfiniteAdeleRing F) :
    ainfReal hF (x + y) = ainfReal hF x + ainfReal hF y := by
  funext v
  exact complReal_add v (hF v) (x v) (y v)

end Coord

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def tensCoord : R ⊗[F] E ≃ₜ (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) :=
  let e := (Module.Free.chooseBasis R (R ⊗[F] E)).equivFun
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem tensCoord_add (x y : R ⊗[F] E) : tensCoord R (x + y) = tensCoord R x + tensCoord R y :=
  map_add (Module.Free.chooseBasis R (R ⊗[F] E)).equivFun x y

end Tens

def flat4 (A B C P : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype P] :
    (A → B → C → P → ℝ) ≃ₜ EuclideanSpace ℝ (A × B × C × P) where
  toFun f := (EuclideanSpace.equiv (A × B × C × P) ℝ).symm (fun k => f k.1 k.2.1 k.2.2.1 k.2.2.2)
  invFun u a b c d := (EuclideanSpace.equiv (A × B × C × P) ℝ u) (a, b, c, d)
  left_inv f := by funext a b c d; simp
  right_inv u := by ext k; simp
  continuous_toFun := (EuclideanSpace.equiv (A × B × C × P) ℝ).symm.continuous.comp (continuous_pi fun k =>
    (continuous_apply k.2.2.2).comp ((continuous_apply k.2.2.1).comp ((continuous_apply k.2.1).comp
      (continuous_apply k.1))))
  continuous_invFun := continuous_pi fun a => continuous_pi fun b => continuous_pi fun c => continuous_pi fun d =>
    (continuous_apply (a, b, c, d)).comp (EuclideanSpace.equiv (A × B × C × P) ℝ).continuous

theorem flatten_four_add (A B C P : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype P] (f g : A → B → C → P → ℝ) :
    flat4 A B C P (f + g) = flat4 A B C P f + flat4 A B C P g := by
  ext k
  simp [flat4]

end PI.AprimeInfW
