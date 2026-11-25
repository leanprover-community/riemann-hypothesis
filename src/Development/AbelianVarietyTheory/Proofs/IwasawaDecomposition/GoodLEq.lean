module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

section Gen

variable {D : D7} (N : TwNew D)

theorem goodL_eq (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) :
    goodL N.toD7 (N.rat S) θ j = goodL D S θ j := by
  have h : N.ex.eLL0 = D.nexp.eLL0 := funext fun g =>
    Subtype.ext (D.what₂.embLL.injective ((N.h0 g).trans (D.nStage_trivialCharacter_coeff_eq g).symm))
  exact congrArg (fun e : G0g D.nd → ↥D.LL0 =>
    Module.End.eigenspace (∑ᶠ g : G0g D.nd, ((e g : ↥D.LL0) : D.what₂.LL) • actL D S j g) 1 ⊓
    ⨅ u : Formalism.IndefR.NX.U D.nd, Module.End.eigenspace (actL D S j u)
      (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) h

def ratIn {S : RatDat D.ntw} (I : RatIn D S) : RatIn N.toD7 (N.rat S) where
  Sb := I.Sb
  rho := I.rho
  chi := I.chi
  ks := I.ks
  fd := I.fd
  mk_fg := I.mk_fg
  hL := I.hL
  hs := I.hs
  hL_zero := I.hL_zero
  θ := I.θ
  θ_ne := I.θ_ne
  eig := I.eig
  span := fun j h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.span j h1 h2
  hL_int := fun j k P h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.hL_int j k P h1 h2

theorem cusp {Rw : RowSide D} (h : RowCusp D Rw) : RowCusp N.toD7 (N.row Rw) := h

theorem mtIn {M tup Q} (h : MtInput D M tup Q) : MtInput N.toD7 (N.mt M) tup Q := { h with }

end Gen

end GlobalTheory.HeightCounting.Up.LiTw

end
