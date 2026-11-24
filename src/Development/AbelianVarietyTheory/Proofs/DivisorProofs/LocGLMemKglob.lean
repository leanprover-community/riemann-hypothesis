module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerTwSplit
open GlobalTheory.EulerTw GlobalTheory.EulerTwU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem theta_mem {v w : Pl E} (f : v.adicCompletion E →+* w.adicCompletion E) (hf : ∀ x, Valued.v (f x) = Valued.v x)
    {g : GLw n v} (hg : g ∈ GlobalTheory.LFun.KGL v (n := n)) :
    thetaGL n (RingHom.id _) (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) (GeneralLinearGroup.map f g) =
      GeneralLinearGroup.map f g := Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) (GeneralLinearGroup.map f g)) * (PhiU n _)⁻¹ ∈ _
  rw [hid]
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n) (GlobalTheory.BCT.LocGlue.intst E n v w f hf g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))


end GlobalTheory.EulerTwSplit
