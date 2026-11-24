module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.Gal.InertialTypesAlt.G

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private def evalEquiv {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    CompletionsOver E v ≃+* w.1.adicCompletion E :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E

private theorem evalEquiv_symm_cont {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    Continuous (evalEquiv w hw).symm :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  (Homeomorph.piUnique fun u : PlacesOver E v => u.1.adicCompletion E).symm.continuous

private def cmpEquiv (n : ℕ) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    GL (Fin n) (CompletionsOver E v) ≃ₜ* Gw n w.1 where
  toFun := GM.cmp w
  invFun := mapGL n ((evalEquiv w hw).symm : w.1.adicCompletion E →+* CompletionsOver E v)
  left_inv g := Units.ext (Matrix.ext fun _ _ => (evalEquiv w hw).symm_apply_apply _)
  right_inv g := Units.ext (Matrix.ext fun _ _ => (evalEquiv w hw).apply_symm_apply _)
  map_mul' := map_mul _
  continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map (evalEquiv_symm_cont w hw))

end

theorem cmpIso : CmpIso := by
  intro F E _ _ _ _ _ n v w hw
  refine ⟨⟨cmpEquiv n w hw, fun _ => rfl⟩, fun g => ⟨fun h => h w, fun h u => ?_⟩, fun h => funext fun g => ?_⟩
  · obtain rfl := hw u
    exact h
  · letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
    exact finprod_unique _

end UpperTheory.Gal.InertialTypesAlt.G
