module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuInvLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace PI.VolStabS.TopoGram

open Matrix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_eq (σ : A →+* A) (J : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (σ : A →+* A) (J G : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (G *ᵥ x) (G *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ G * J * G) x y := by
  rw [hform_eq, hform_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, Formalism.UG.cT, vecMul_transpose]
  congr 1
  funext i
  exact RingHom.map_mulVec σ G x i

end PI.VolStabS.TopoGram

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Matrix
open scoped TensorProduct

theorem gramPres_holds : GramPres := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet g X
  have hg : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR (AF F) J *
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _) =
      JR (AF F) J := g.2
  funext x y
  change hR (AF F) σ J (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X x) (((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) *ᵥ X y) = hR (AF F) σ J (X x) (X y)
  rw [hR, TopoGram.hform_mulVec, hg]
  rfl

end PI.VolStabS
