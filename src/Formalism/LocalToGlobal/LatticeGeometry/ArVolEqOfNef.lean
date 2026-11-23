module

public import Formalism.LocalRingCardinality.DataDIV
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

variable {D : D7}

structure AlgPkg (G : DV.Geo D.what₂.LL) (Tau : Type) [Fintype Tau] (N : ℕ) (Comp : Type) [Fintype Comp] where

  Yv : Comp → G.Var

  Ybd : ∀ c, G.Cl (Yv c)

  bd : ∀ c, G.Dv (Yv c)
  bd_supp : ∀ c, G.supp (Yv c) (bd c) = Ybd c

  Lw : ∀ c, (Tau → Fin N → ℤ) →+ G.Dv (Yv c)

  dim_eq : ∀ c, G.dim (Yv c) = Formalism.DegreeFormula.dimFl Tau N

  degA : ∀ c, G.Adl (Yv c) → ℝ

  degA_ofW : ∀ c (Δ : G.Dv (Yv c)) (W : HLat D.what₂.LL) (ι : W.V →ₗ[D.what₂.LL] G.Fn (Yv c)),
    degA c (G.ofW (Yv c) Δ W ι) = (G.inter (Yv c) (fun _ => Δ) : ℝ)

  degA_twist : ∀ c Lb ci cf, degA c (G.twist (Yv c) Lb ci cf) = degA c Lb

  semipos : (∀ c, G.Adl (Yv c)) → Prop
  nefFib : (∀ c, G.Adl (Yv c)) → Prop

  Mbar : ℝ → (Tau → Fin N → ℝ) → ℚ → ∀ c, G.Adl (Yv c)

namespace AlgPkg

variable {G : DV.Geo D.what₂.LL} {Tau : Type} [Fintype Tau] {N : ℕ} {Comp : Type} [Fintype Comp]
  (A : AlgPkg G Tau N Comp)

def ALB : Type := ∀ c, G.Adl (A.Yv c)

def arSelfC (L : A.ALB) (c : Comp) : ℝ := G.arTop (A.Yv c) (L c)

def geoC (L : A.ALB) (c : Comp) : ℝ := A.degA c (L c)

def arVol (L : A.ALB) : ℝ := ∑ c, G.arVol (A.Yv c) (L c)

def arNef (L : A.ALB) : Prop := ∀ c, G.nefA (A.Yv c) (L c)

end AlgPkg

end Formalism.L2.Geo
