module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwCentSwTw
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem thetaGL_id_mem {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) {g : GLw n w}
    (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) : thetaGL n (RingHom.id _) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) g = g :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) g) * (PhiU n _)⁻¹ ∈ _
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n)
    (GlobalTheory.BCT.LocGlue.intst E n w w (RingHom.id _) (fun _ => rfl) g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))

theorem sgP_facts : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
    Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧
      ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  intro E _ _ a b w
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.LocTwist.continuous_thetaGL a (RingHom.id _) continuous_id).prodMap
      (GlobalTheory.LocTwist.continuous_thetaGL b (RingHom.id _) continuous_id)
  · rintro ⟨g₁, g₂⟩
    exact Prod.ext (GlobalTheory.LocTwist.thetaGL_thetaGL a (RingHom.id _) (fun _ => rfl) g₁)
      (GlobalTheory.LocTwist.thetaGL_thetaGL b (RingHom.id _) (fun _ => rfl) g₂)
  · rintro ⟨k₁, k₂⟩ hk
    exact ⟨thetaGL_id_mem a w hk.1, thetaGL_id_mem b w hk.2⟩

end GlobalTheory.CompanionTheory.LocalHypotheses

end
