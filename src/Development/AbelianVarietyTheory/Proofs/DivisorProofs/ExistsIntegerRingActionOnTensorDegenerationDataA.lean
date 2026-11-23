module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataSymmetricPullbackAndPsiEqTauStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationTauBalancedOfAdjointIntMatriceStatement
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensAct

theorem exists_integer_ring_action_on_tensor_degeneration_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) ∧ (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) := by
  intro R _ _ _ hR E _ _ _ H D D' r W hpos hdet T ρ hρ hw
  letI := H.starRing
  letI md : Module (𝓞 E) D'.toPre.X := tensModule T ρ
  let oB : D'.toPre.P.OAct (𝓞 E) :=
    { ringAct T ρ with rosati := fun a ↦ GlobalTheory.T.rosatiAdj_tensorPowerIntMatrixEndomorphism R D.toPre D'.toPre W T (ρ a) (ρ (star a)) (hρ a) }
  let o : D'.toPre.OAct (𝓞 E) :=
    { onB := oB
      c_lin := fun a y ↦ c_lin T (ρ a) y
      tau_bal := fun a ↦ GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices R _ D D' W T (ρ a) (ρ (star a)) (hρ a) }
  exact ⟨md, o, ⟨fun a z i ↦ xe_latAct T (ρ a) z i, fun a i ↦ matAct_pr T (ρ a) i⟩,
    GlobalTheory.T.traceFormTwistIso_of_matAct_of_latAct R _ D D' W T (ρ H.w0) (𝓞 E) o H.w0 rfl (fun y ↦ rfl) hw⟩

end GlobalTheory.TensAct
