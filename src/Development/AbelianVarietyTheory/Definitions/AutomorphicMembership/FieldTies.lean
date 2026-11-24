module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.AtMember

variable {D : D7}

structure CorePin (J : Core D) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop where
  laws : LawsCore J
  canon : J.Q.Canon
  rank : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q
  pb : J.pb = pb

theorem CorePin.reCore {J : CoreJ D} {pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)} (h : CorePin J.toCore pb) {dict mu chiW x₀ cE}
    (hM : LawsM (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore) : CorePin (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore pb :=
  ⟨⟨hM, h.laws.cuspMul, h.laws.latZ, h.laws.cuNe, h.laws.expo⟩, h.canon, h.rank, h.pb⟩

structure FieldTies (D : D7) (C : Formalism.L2.Host.CharFrame D) : Prop where
  one : FieldOK0 D D.host.pde
  two : FieldOK0 D D.host.pde'
  del : ∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D
  del' : ∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D
  small : ∀ L : ℝ, HostSz D.host L → Sz (FO D) (poR D.R L) (poR D.R L)

def HalfAt (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def NumAtL (L : SizeData₂ D) (x : ℝ) : Prop :=
  DV.KapDef D ∧ (∃ (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm), GlobalTheory.BigOn.PageNum Tp x) ∧ FieldSmall D L

end GlobalTheory.AtMember
