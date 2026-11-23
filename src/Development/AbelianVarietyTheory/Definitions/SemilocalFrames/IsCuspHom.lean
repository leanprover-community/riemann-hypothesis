module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.RowLev

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev ModInst (D : D7) (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (pl : InfinitePlace D.host.F ≃ D.what₂.Tau) : Type :=
  InstData D.sp.cm V (fun v => M.ε (pl v)) (fun v => tauE D (pl v))

def levHom (I : AutInst) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (J : Set I.Gf) (χ : I.Gf → ℂ) :
    Set (Hs →L[ℂ] I.L2 μf fund) :=
  {A | A ∈ I.HomS σs μf fund R ∧ ∀ k ∈ J, (R (1, k)).comp A = χ k • A}

def IsCuspHom (I : AutInst) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {μf : Measure I.Gf} [SigmaFinite μf] {fund : Set I.GA} (A : Hs →L[ℂ] I.L2 μf fund) : Prop :=
  ∀ u, I.IsCuspFn (I.muA μf) (I.ext (A u))

end GlobalTheory.RowLev
