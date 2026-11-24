module

public import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization
public import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.AlgClosedOfAic
public import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.OpenPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.SimpleRing.Principal
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf.AICPf

def AffAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W)
  [QuasiCompact g] [QuasiSeparated g] (U : W.Opens), IsAffineOpen U →
  GlobalTheory.EtC.AIC Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U)

def LocAIC : Prop := ∀ (X : Scheme.{0}) [IsIntegral X],
  (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ GlobalTheory.EtC.AIC Γ(X, U)) → AICSch X

theorem normAIC_of (ha : AffAIC) (hl : LocAIC) : NormAIC := by
  intro K _ _ W g _ _
  refine ⟨inferInstance, ?_⟩
  have := hl g.normalization ?_
  · exact this.2
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.fromNormalization x)) isOpen_univ
  exact ⟨g.fromNormalization ⁻¹ᵁ U, hxU, hU.preimage _, ha K g U hU⟩

theorem norm_full (ha : AffAIC) (hl : LocAIC) : LateralTheory.E.ChowCut.Norm :=
  Norm_of OpenPf.openNbhdIC FFPf.ffAlg (normAIC_of ha hl)

end LateralTheory.E.NormPf.AICPf

end
