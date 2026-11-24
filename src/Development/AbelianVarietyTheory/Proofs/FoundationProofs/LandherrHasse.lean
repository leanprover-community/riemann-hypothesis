module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteOrthonormal

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_orthonormal (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    ∃ b : Fin W.rank → W.V, LinearIndependent E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.DefiniteMass.exists_isometry hc W hs hp
  refine ⟨(Pi.basisFun E (Fin W.rank)).map e.symm, Module.Basis.linearIndependent _, fun a c => ?_⟩
  rw [← he]
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  change ∑ i, star ((Pi.single a (1 : E) : Fin W.rank → E) i) * (Pi.single c (1 : E) : Fin W.rank → E) i = _
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

end

theorem landherrHasse : ∀ D : D7, LandherrHasse D := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W hs hp => exists_orthonormal (E := D.host.E) D.sp.cm.cmUnram W hs hp

end GlobalTheory.DefiniteOrthonormal
