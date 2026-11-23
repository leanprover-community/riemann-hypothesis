module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open GlobalTheory.LFun.ConjPlace (invT dGL apply_heckeVec_shift Tj_invT Tj_shift_self map_mem_Ov_iff mem_iff_invT satEig_inv_mul satEig_zero)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ThetaSatPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {u w : Pl E}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem embT_cw (a : ℕ) (u : Pl E) (g : GLw a (GlobalTheory.ThetaSatake.cw u)) :
    embT a (GlobalTheory.ThetaSatake.cw u) g =
      embW a u (PhiU a _ * invT (GlobalTheory.ThetaSatake.cloc u) a g * (PhiU a _)⁻¹) := by
  change GlobalTheory.ThetaPull.thetaA E a (finGL E a (locGL E a (GlobalTheory.ThetaSatake.cw u) g)) = finGL E a (locGL E a u _)
  rw [GlobalTheory.ThetaPull.thetaA_finGL, GlobalTheory.ThetaSatake.theta_locGL, GlobalTheory.ThetaSatake.thetaGL_conj]

theorem invT_symm {K K' : Type} [Field K] [Field K'] (c : K ≃+* K') (n : ℕ) (g : GL (Fin n) K') :
    (invT c n).symm g = invT c.symm n g := rfl

end GlobalTheory.CompanionTheory.ThetaSatPair
